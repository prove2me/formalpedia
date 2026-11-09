-- Prove2me | Theorems.Thm_IntADSat_prop_A_2
-- name    : IntADSat.prop_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:11.092917+00:00
-- url     : https://prove2.me/theorems/d4c42329-1cd3-4479-95fa-eebfb05998ec
-- title:
--   Proposition A.2 — local criterion for $p$-AD-saturation
-- statement:
--   Let $G$ be a simple graph on $[n]$ with word lattice $\Lambda_G=\mathbb Z\langle A,D\rangle e$, let $r_G=\dim_{\mathbb Q}\mathbb Q\langle A,D\rangle e$ and $I_G=|\mathbb Z^n/\Lambda_G|$, and let $p$ be a prime. The following are equivalent:
--
--   1. $G$ is $p$-AD-saturated: $M_p(G)=\mathbb F_p\langle A,D\rangle e=\mathbb F_p^n$;
--   2. $\Lambda_G+p\mathbb Z^n=\mathbb Z^n$;
--   3. $\Lambda_G\otimes_{\mathbb Z}\mathbb Z_p=\mathbb Z_p^n$, where $\mathbb Z_p$ is the ring of $p$-adic integers;
--   4. $r_G=n$ and $p\nmid I_G$.
--
--   Consequently integral AD-saturation is equivalent to $p$-AD-saturation for every prime:
--
--   $$
--   \Lambda_G=\mathbb Z^n\iff M_q(G)=\mathbb F_q^n\ \text{ for every prime } q .
--   $$
--
--   This is the local-global principle that reduces Theorem 1.1 to estimates at each prime.
--
--   **Formalization Note** Condition 3 is the $\mathbb Z_p$-span of the image of $\Lambda_G$ in $\mathbb Z_p^n$ being everything; $I_G$ is `Nat.card` of the quotient, which is finite (and equals the paper's $I_G$) when $r_G=n$.
--
--   Differences from the source:
--   - encoding: Λ_G ⊗_ℤ ℤ_p = ℤ_pⁿ → the ℤ_[p]-span of the image of Λ_G in ℤ_[p]ⁿ is ⊤; reason: ℤ_p is flat over ℤ, so Λ_G ⊗ ℤ_p maps isomorphically onto that span
--   - encoding: I_G = |C_G| (defined for AD-full graphs) → Nat.card of ℤⁿ/Λ_G, conjoined with r_G = n; reason: under r_G = n the quotient is finite and Nat.card is I_G
--   - encoding: Λ_G + pℤⁿ = ℤⁿ → every x ∈ ℤⁿ is y + p·z with y ∈ Λ_G, z ∈ ℤⁿ; reason: same subgroup equation
--   - generalization: graphs with at least one vertex (Appendix A convention) → every n, including n = 0; reason: at n = 0 every condition and both sides of the equivalence hold trivially; the statement specializes to n ≥ 1
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Proposition A.2, pp.11–12 (PDF 12–13)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_wordModule

set_option autoImplicit false

namespace IntADSat

/-- **Proposition A.2 (Local criterion)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), pp.11–12 (PDF 12–13)). For every graph and prime
`p` the following are equivalent: (1) `G` is `p`-AD-saturated, `M_p(G) = 𝔽_pⁿ`; (2)
`Λ_G + pℤⁿ = ℤⁿ`; (3) `Λ_G ⊗_ℤ ℤ_p = ℤ_pⁿ`; (4) `r_G = n` and `p ∤ I_G`. Consequently integral
AD-saturation is equivalent to `p`-AD-saturation for every prime.

**Formalization Note** (3) is the `ℤ_p`-span of the image of `Λ_G` in `ℤ_pⁿ` (`ℤ_p` is flat over `ℤ`,
so `Λ_G ⊗ ℤ_p` is that span); `r_G = dim_ℚ ℚ⟨A, D⟩e`; `I_G = |ℤⁿ/Λ_G|` as `Nat.card` (when
`r_G = n` the quotient is finite and this is the paper's `I_G`). -/
theorem prop_A_2 {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℕ) [Fact p.Prime] :
    List.TFAE
      [wordModule (ZMod p) G = ⊤,
       ∀ x : Fin n → ℤ, ∃ y ∈ wordLattice G, ∃ z : Fin n → ℤ, x = y + (p : ℤ) • z,
       Submodule.span ℤ_[p] ((fun x : Fin n → ℤ => fun i => ((x i : ℤ) : ℤ_[p])) '' (wordLattice G : Set (Fin n → ℤ))) = ⊤,
       Module.finrank ℚ (wordModule ℚ G) = n ∧ ¬ p ∣ Nat.card ((Fin n → ℤ) ⧸ wordLattice G)] ∧
    (wordLattice G = ⊤ ↔ ∀ q : ℕ, q.Prime → wordModule (ZMod q) G = ⊤) := by sorry

end IntADSat
