-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_reduced_density_recursion
-- name    : NonAbelianDMNRG.Recursion.reduced_density_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:24.891955+00:00
-- url     : https://prove2.me/theorems/0d9e33f4-0260-427b-8f20-232f3c8c772f
-- title:
--   §III, eqs. (42)–(45) — tracing out a site keeps $R$ symmetric and gives the $\dim(\tilde\imath)/\dim(u)$ recursion for its kept block
-- statement:
--   This is the reduced-density-matrix recursion of the density matrix numerical renormalization group (DM-NRG) for non-Abelian symmetries, for one tracing step.
--
--   **Setting.** Let $G$ be a group and let each label $Q$ carry a unitary representation $\pi_Q$ on $\mathbb C^{\dim Q}$. Assume
--   1. every $\pi_Q$ is irreducible, and representations with distinct labels are inequivalent;
--   2. for labels $q, Q$ a finite set of labels $Q'$ (one copy each) and generalized Clebsch–Gordan matrices $C^{Q'}_{qQ}$ with entries $\langle q\,q^z; Q\,Q^z\mid Q'\,Q'^z\rangle$ are given, which are isometric ($C^\dagger C = 1$), intertwining ($(\pi_q(g)\otimes\pi_Q(g))C = C\pi_{Q'}(g)$) and complete ($\sum_{Q'} C C^\dagger = 1$);
--   3. $K$ is a finite set of kept multiplets $u$ (labels $Q_u$) of iteration $n-1$ and $\Lambda$ a finite set of local multiplets $\mu$ (labels $q_\mu$) of site $n$;
--   4. $R$ is an operator on the new space spanned by $|u, Q^z_u; \mu, q^z_\mu\rangle$ that is scalar under the symmetry: $U(g) R U(g)^\dagger = R$ for all $g$, with $U(g) = V(g)\otimes L(g)$.
--
--   Let $|\tilde\imath, Q^z\rangle$ be the canonical basis (21), where $\tilde\imath = ((u,\mu), Q_{\tilde\imath})$ is constructed from $u$ and $\mu$ ($\tilde\imath \Leftarrow u$).
--
--   **Conclusion.**
--   1. (42) The kept block $\operatorname{Tr}_{\mathrm{site}}\{R\}$ is scalar: $V(g)\operatorname{Tr}_{\mathrm{site}}\{R\}V(g)^\dagger = \operatorname{Tr}_{\mathrm{site}}\{R\}$ for all $g$.
--   2. (43)–(44) There are reduced matrix elements $r(\tilde\imath,\tilde\jmath) = \langle\tilde\imath\Vert\tilde R\Vert\tilde\jmath\rangle$ with $\langle\tilde\imath, Q^z\mid R\mid\tilde\jmath, Q^{z\prime}\rangle = r(\tilde\imath,\tilde\jmath)\,\delta_{Q_{\tilde\imath},Q_{\tilde\jmath}}\delta_{Q^z,Q^{z\prime}}$.
--   3. (45) For every such family $r$ and all kept $u, v$ with $Q_u = Q_v$,
--   $$
--   \langle u, Q^z \mid \operatorname{Tr}_{\mathrm{site}}\{R\} \mid v, Q^{z\prime}\rangle = \delta_{Q^z,Q^{z\prime}} \sum_{\mu\in\Lambda}\ \sum_{\tilde\imath \Leftarrow (u,\mu)}\ \sum_{\tilde\jmath\Leftarrow (v,\mu)} \frac{\dim(\tilde\imath)}{\dim(u)}\, r(\tilde\imath,\tilde\jmath)\,\delta_{Q_{\tilde\imath},Q_{\tilde\jmath}} ,
--   $$
--   so the common diagonal value is the paper's reduced element $\langle u\Vert R^{[n-1]}\Vert v\rangle$.
--   4. (43) at iteration $n-1$: $\langle u, Q^z \mid \operatorname{Tr}_{\mathrm{site}}\{R\}\mid v, Q^{z\prime}\rangle = 0$ whenever $Q_u\neq Q_v$.
--
--   The recursion lets DM-NRG compute the reduced density matrices $R^{[n]}$ entirely in terms of reduced matrix elements, one number per pair of multiplets, for essentially any symmetry; the paper's truncated reduced density matrix $R^{[n]}$ of (38) is one instance of $R$.
--
--   **Formalization Note** One abstract group with labelled irreducible unitary representations replaces the paper's product $G_1\times\dots\times G_\Gamma$. The coupling is multiplicity-free. In (45) the sum over $\tilde\imath,\tilde\jmath,q_\mu,\mu$ pairs $\tilde\imath$ and $\tilde\jmath$ built with the same local multiplet $\mu$; $\dim(\tilde\imath) = \dim Q_{\tilde\imath}$, $\dim(u) = \dim Q_u$. The hypothesis $Q_u = Q_v$ is where the paper's left-hand side exists; part 4 covers $Q_u\neq Q_v$. Internal quantum numbers of multiplets with equal labels are compared by value. Operators on the new space are indexed block first, Clebsch–Gordan matrices local first; no fermionic sign factors arise. The reduced elements in part 3 are tied to $R$ by the hypothesis of part 3, and part 2 shows such a family exists.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, eqs. (42)–(45)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **§III, eqs. (42)–(45), p. 7 (the reduced-density-matrix recursion).** Let the labels carry
irreducible, pairwise inequivalent unitary representations of `G`, let the generalized
Clebsch–Gordan matrices be isometric, intertwining and complete (multiplicity-free coupling), and
let `R` on the new space (kept block states × local states of the site) be invariant under
`U(g) = V(g) ⊗ L(g)`. Then
1. (42) `Tr_site R` is invariant under `V(g)`;
2. (43)–(44) `R` is diagonal in the canonical basis, with reduced matrix elements `r ĩ j̃`;
3. (45) for every such `r` and kept multiplets `u, v` with `Q_u = Q_v`,
   `(Tr_site R)(⟨u, a⟩, ⟨v, b⟩) = δ_{a, b} Σ_µ Σ_{ĩ ⇐ (u, µ)} Σ_{j̃ ⇐ (v, µ)}
   δ_{Q_ĩ, Q_j̃} (dim Q_ĩ / dim Q_u) r ĩ j̃`;
4. (43) at iteration `n − 1`: `(Tr_site R)(⟨u, a⟩, ⟨v, b⟩) = 0` when `Q_u ≠ Q_v`. -/
theorem reduced_density_recursion {G : Type} [Group G] {Lab : Type} [DecidableEq Lab] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (hirr : ∀ Q : Lab, Representation.IsIrreducible (labelRep dim π Q))
    (hineq : ∀ Q Q' : Lab, Q ≠ Q' →
      IsEmpty (Representation.Equiv (labelRep dim π Q) (labelRep dim π Q')))
    (couple : Lab → Lab → Finset Lab)
    (cg : (q Q Q' : Lab) → Matrix (Fin (dim q) × Fin (dim Q)) (Fin (dim Q')) ℂ)
    (hiso : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, (cg q Q Q')ᴴ * cg q Q Q' = 1)
    (hint : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, ∀ g : G,
      ((π q g : Matrix (Fin (dim q)) (Fin (dim q)) ℂ) ⊗ₖ
          (π Q g : Matrix (Fin (dim Q)) (Fin (dim Q)) ℂ)) * cg q Q Q' =
        cg q Q Q' * (π Q' g : Matrix (Fin (dim Q')) (Fin (dim Q')) ℂ))
    (hcompl : ∀ q Q : Lab, ∑ Q' ∈ couple q Q, cg q Q Q' * (cg q Q Q')ᴴ = 1)
    {K Λ : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (Qu : K → Lab) (ql : Λ → Lab)
    (R : Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim Qu × Multiplets dim ql) ℂ)
    (hR : ∀ g : G, newRep dim π Qu ql g * R * (newRep dim π Qu ql g)ᴴ = R) :
    -- (42): the kept block `Tr_site R` is invariant under `V(g)`
    (∀ g : G, multipletRep dim π Qu g * WildeQIT.partialTraceRight R *
        (multipletRep dim π Qu g)ᴴ = WildeQIT.partialTraceRight R) ∧
    -- (43)–(44): `R` is scalar in the canonical basis (21)
    (∃ r : Can couple Qu ql → Can couple Qu ql → ℂ,
      ∀ (i j : Can couple Qu ql) (m : Fin (dim (canLabel couple Qu ql i)))
        (m' : Fin (dim (canLabel couple Qu ql j))),
        ((canonicalBasis dim couple cg Qu ql)ᴴ * R * canonicalBasis dim couple cg Qu ql)
            ⟨i, m⟩ ⟨j, m'⟩ =
          if canLabel couple Qu ql i = canLabel couple Qu ql j ∧ m.val = m'.val then r i j
          else 0) ∧
    -- (45): the recursion for the kept matrix elements, for every reduced-element family `r` of `R`
    (∀ r : Can couple Qu ql → Can couple Qu ql → ℂ,
      (∀ (i j : Can couple Qu ql) (m : Fin (dim (canLabel couple Qu ql i)))
        (m' : Fin (dim (canLabel couple Qu ql j))),
        ((canonicalBasis dim couple cg Qu ql)ᴴ * R * canonicalBasis dim couple cg Qu ql)
            ⟨i, m⟩ ⟨j, m'⟩ =
          if canLabel couple Qu ql i = canLabel couple Qu ql j ∧ m.val = m'.val then r i j
          else 0) →
      ∀ (u v : K), Qu u = Qu v → ∀ (a : Fin (dim (Qu u))) (b : Fin (dim (Qu v))),
        WildeQIT.partialTraceRight R ⟨u, a⟩ ⟨v, b⟩ =
          if a.val = b.val then
            ∑ l : Λ, ∑ Q' : couple (ql l) (Qu u), ∑ Q'' : couple (ql l) (Qu v),
              if (Q' : Lab) = (Q'' : Lab) then
                ((dim (Q' : Lab) : ℂ) / (dim (Qu u) : ℂ)) * r ⟨(u, l), Q'⟩ ⟨(v, l), Q''⟩
              else 0
          else 0) ∧
    -- (43) at iteration `n − 1`: kept multiplets with different labels do not couple
    (∀ (u v : K), Qu u ≠ Qu v → ∀ (a : Fin (dim (Qu u))) (b : Fin (dim (Qu v))),
      WildeQIT.partialTraceRight R ⟨u, a⟩ ⟨v, b⟩ = 0) := by sorry

end NonAbelianDMNRG.Recursion
