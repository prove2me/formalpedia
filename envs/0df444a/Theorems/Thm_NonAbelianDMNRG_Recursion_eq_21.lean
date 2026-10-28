-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_eq_21
-- name    : NonAbelianDMNRG.Recursion.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:01.94292+00:00
-- url     : https://prove2.me/theorems/54171eae-3bc5-4bc2-ba43-d8dc3a04e6fb
-- title:
--   Eq. (21) — the canonical basis is orthonormal, complete and transforms as irreducible multiplets
-- statement:
--   Let $G$ be a group whose labels $Q$ carry unitary representations $\pi_Q$. For labels $q, Q$ let a finite set of labels $Q'$ (those occurring in $q\otimes Q$, one copy each) be given, and for each such $Q'$ a generalized Clebsch–Gordan matrix $C = C^{Q'}_{qQ}$ with entries $\langle q\,q^z; Q\,Q^z\mid Q'\,Q'^z\rangle$, satisfying
--   1. isometry: $C^\dagger C = 1$;
--   2. intertwining: $(\pi_q(g)\otimes\pi_Q(g))\, C = C\, \pi_{Q'}(g)$ for all $g\in G$;
--   3. completeness: $\sum_{Q'} C^{Q'}_{qQ} (C^{Q'}_{qQ})^\dagger = 1$ on $\mathbb C^{\dim q}\otimes\mathbb C^{\dim Q}$.
--
--   Let $K$ (kept multiplets $u$ with labels $Q_u$) and $\Lambda$ (local multiplets $\mu$ with labels $q_\mu$) be finite, and let $|\tilde\imath, Q_{\tilde\imath}, Q^z_{\tilde\imath}\rangle$ be the canonical states of (21),
--   $$
--   |\tilde\imath, Q_{\tilde\imath}, Q^z_{\tilde\imath}\rangle = \sum_{Q^z_u,\,q^z_\mu} \langle q_\mu q^z_\mu; Q_u Q^z_u \mid Q_{\tilde\imath} Q^z_{\tilde\imath}\rangle\, |u, Q_u, Q^z_u; \mu, q_\mu, q^z_\mu\rangle .
--   $$
--   Then
--   1. (orthonormality) $\langle \tilde\imath, Q^z \mid \tilde\jmath, Q^{z\prime}\rangle = \delta_{\tilde\imath\tilde\jmath}\delta_{Q^z Q^{z\prime}}$;
--   2. (completeness) $\sum_{\tilde\imath, Q^z} |\tilde\imath, Q^z\rangle\langle\tilde\imath, Q^z| = 1$ on the new space;
--   3. (transformation law) $U(g)\, |\tilde\imath, Q^z\rangle = \sum_{Q^{z\prime}} \pi_{Q_{\tilde\imath}}(g)_{Q^{z\prime} Q^z}\, |\tilde\imath, Q^{z\prime}\rangle$ for all $g$, with $U(g) = V(g)\otimes L(g)$.
--
--   In matrix form: the matrix $E$ whose columns are the canonical states is unitary and satisfies $U(g)E = E\bigoplus_{\tilde\imath}\pi_{Q_{\tilde\imath}}(g)$. This is the precise sense in which the canonical states "transform as irreducible multiplets".
--
--   **Formalization Note** The Clebsch–Gordan matrices are indexed local first, $((q^z, Q^z), Q'^z)$, as in (21); the new space is indexed block first. Irreducibility is not needed for this statement.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 4, eq. (21)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **Eq. (21), p. 4 (the canonical basis).** Let the generalized Clebsch–Gordan matrices be
isometries that intertwine `π q ⊗ π Q` with `π Q'` and resolve the identity on `q ⊗ Q`. Then the
canonical states `|ĩ, Q_ĩ, Q^z_ĩ⟩` of (21) (a) are orthonormal, (b) form a complete basis of the
new space, and (c) transform as irreducible multiplets under `U(g)`:
`U(g) |ĩ, Q^z⟩ = Σ_{Q^z'} (π Q_ĩ g)_{Q^z' Q^z} |ĩ, Q^z'⟩`. -/
theorem eq_21 {G : Type} [Group G] {Lab : Type} [DecidableEq Lab] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (couple : Lab → Lab → Finset Lab)
    (cg : (q Q Q' : Lab) → Matrix (Fin (dim q) × Fin (dim Q)) (Fin (dim Q')) ℂ)
    (hiso : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, (cg q Q Q')ᴴ * cg q Q Q' = 1)
    (hint : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, ∀ g : G,
      ((π q g : Matrix (Fin (dim q)) (Fin (dim q)) ℂ) ⊗ₖ
          (π Q g : Matrix (Fin (dim Q)) (Fin (dim Q)) ℂ)) * cg q Q Q' =
        cg q Q Q' * (π Q' g : Matrix (Fin (dim Q')) (Fin (dim Q')) ℂ))
    (hcompl : ∀ q Q : Lab, ∑ Q' ∈ couple q Q, cg q Q Q' * (cg q Q Q')ᴴ = 1)
    {K Λ : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (Qu : K → Lab) (ql : Λ → Lab) :
    (canonicalBasis dim couple cg Qu ql)ᴴ * canonicalBasis dim couple cg Qu ql = 1 ∧
    canonicalBasis dim couple cg Qu ql * (canonicalBasis dim couple cg Qu ql)ᴴ = 1 ∧
    ∀ g : G, newRep dim π Qu ql g * canonicalBasis dim couple cg Qu ql =
      canonicalBasis dim couple cg Qu ql * multipletRep dim π (canLabel couple Qu ql) g := by sorry

end NonAbelianDMNRG.Recursion
