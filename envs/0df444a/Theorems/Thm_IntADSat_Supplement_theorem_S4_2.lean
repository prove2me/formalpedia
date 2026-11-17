-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_S4_2
-- name    : IntADSat.Supplement.theorem_S4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:57:14.519078+00:00
-- url     : https://prove2.me/theorems/3d2f90a7-deea-425a-a241-bb644d41b184
-- title:
--   Theorem S4.2 — index and denominator constraints: $I_G=I_H$, $\ell(Q)\mid\gcd(c_G,c_H)$, integrality at $p\nmid I_G$
-- statement:
--   Let $G$ be an AD-full graph on $n\ge1$ vertices and $H$ a finite simple graph with $\mu_H=\mu_G$ (the hypotheses of Lemma S4.1), and let $Q$ be the rational orthogonal matrix with $Qe=e$, $QA_G=A_HQ$, $QD_G=D_HQ$. Write $I_G=|\mathbb Z^n/\Lambda_G|$ and $c_G=\exp(\mathbb Z^n/\Lambda_G)$, and likewise for $H$. Then
--   $$I_G=I_H .$$
--   If $\ell(Q)$ is the least positive integer such that $\ell(Q)Q$ is integral, then
--   $$\ell(Q)\mid\gcd(c_G,c_H).$$
--   Consequently, if $p$ is a prime with $p\nmid I_G$, then $Q$ is integral over $\mathbb Z_{(p)}$ (every entry has denominator prime to $p$) and over $\mathbb Z_p$ (every entry lies in the $p$-adic integers).
--
--   The index is therefore constant on a full principal moment fibre, and the denominators of the intertwiner are confined to the primes dividing the defect.
--
--   Differences from the source:
--   - encoding: the hypotheses of Lemma S4.1, Q the unique pointed isometry → G AD-full, 0 < n, MomentEquiv G H, and every Q with IsPointedIntertwiner G H Q; reason: Q is unique by Theorem A.8, so quantifying over all such Q is the same statement
--   - encoding: I_G = |C_G|, c_G = exp(C_G) with exponent 1 for the trivial group → Nat.card and AddMonoid.exponent of ℤⁿ/Λ_G; reason: Mathlib's exponent of the trivial group is 1; the base mission uses Nat.card for I_G
--   - encoding: Q integral over ℤ_(p) and over ℤ_p → every entry has denominator not divisible by p; every entry, in ℚ_p, is the image of a p-adic integer; reason: definitions of the two local rings
--   - encoding: H a finite simple graph → H : SimpleGraph (Fin m) for every m; reason: every finite simple graph is isomorphic to one on Fin m, and moments and isomorphism are invariant under relabelling; the empty-word moment forces m = n
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S4.2, p.39 (PDF 40); Lemma S4.1, p.39 (PDF 40)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_Supplement_MomentEquiv
import Definitions.Def_IntADSat_Supplement_IsPointedIntertwiner
import Definitions.Def_IntADSat_Supplement_level

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Theorem S4.2 (Index and denominator constraints)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.39 (PDF 40)). Under the hypotheses of
Lemma S4.1 (`G` AD-full and `μ_H = μ_G`, with `Q` the pointed rational orthogonal intertwiner),
`I_G = I_H`. If `ℓ(Q)` is the least positive integer such that `ℓ(Q)Q` is integral, then
`ℓ(Q) ∣ gcd(c_G, c_H)`. Consequently, if `p ∤ I_G`, then `Q` is integral over `ℤ_(p)` and over `ℤ_p`.

**Formalization Note** `I_G = |ℤⁿ/Λ_G|` (`Nat.card`, as in the base mission) and `c_G` is the exponent
(`AddMonoid.exponent`, which is `1` for the trivial group) of `ℤⁿ/Λ_G`. The conclusions are stated for every
pointed intertwiner `Q` (it is unique by Theorem A.8). `Q` integral over `ℤ_(p)`: every entry has denominator
prime to `p`; over `ℤ_p`: every entry, in `ℚ_p`, lies in `ℤ_p`. `p` is any prime. -/
theorem theorem_S4_2 {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (hn : 0 < n)
    (hG : Module.finrank ℚ (IntADSat.wordModule ℚ G) = n) (hμ : MomentEquiv G H)
    (Q : Matrix (Fin m) (Fin n) ℚ) (hQ : IsPointedIntertwiner G H Q) :
    Nat.card ((Fin n → ℤ) ⧸ IntADSat.wordLattice G) =
        Nat.card ((Fin m → ℤ) ⧸ IntADSat.wordLattice H) ∧
    level Q ∣ Nat.gcd (AddMonoid.exponent ((Fin n → ℤ) ⧸ IntADSat.wordLattice G))
        (AddMonoid.exponent ((Fin m → ℤ) ⧸ IntADSat.wordLattice H)) ∧
    ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Nat.card ((Fin n → ℤ) ⧸ IntADSat.wordLattice G) →
      (∀ i j, ¬ p ∣ (Q i j).den) ∧
      (∀ i j, ∃ z : ℤ_[p], (z : ℚ_[p]) = ((Q i j : ℚ) : ℚ_[p])) := by sorry

end IntADSat.Supplement
