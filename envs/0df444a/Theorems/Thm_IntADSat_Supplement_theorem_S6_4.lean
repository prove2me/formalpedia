-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_S6_4
-- name    : IntADSat.Supplement.theorem_S6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:59:15.850464+00:00
-- url     : https://prove2.me/theorems/1825c145-3a60-4dd9-a497-8fe28ecc7abe
-- title:
--   Theorem S6.4 — binary obstruction: even weight, and $\mathrm{wt}(v)\equiv2\pmod4$ certifies rigidity without saturation
-- statement:
--   Let $G$ be a graph on $n$ vertices with $I_G=|\mathbb Z^n/\Lambda_G|=2$. Then there is a unique nonzero vector $v\in\{0,1\}^{V(G)}$ orthogonal modulo $2$ to all AD word vectors $w(A_G,D_G)e$. This $v$ has even Hamming weight. If
--   $$\mathrm{wt}(v)\equiv2\pmod 4,$$
--   then $G$ is determined by its principal moments (every finite simple graph $H$ with $H\equiv_\mu G$ is isomorphic to $G$), although it is not integrally AD-saturated ($\Lambda_G\neq\mathbb Z^n$).
--
--   The theorem separates principal-moment rigidity from integral saturation: Example S6.7 is a graph of this kind.
--
--   Differences from the source:
--   - encoding: I_G = 2 → Nat.card (ℤⁿ/Λ_G) = 2; reason: the base mission's convention for I_G; a finite quotient forces AD-fullness, which I_G presupposes
--   - reading: let v represent the unique nonzero vector orthogonal modulo 2 to all AD word vectors → conclusion ∃! v with IsBinaryObstruction G v, and the remaining conclusions for every such v; reason: the theorem asserts existence and uniqueness through "the unique"
--   - encoding: v ∈ {0,1}^{V(G)}; Hamming weight → v : Fin n → ZMod 2; wt(v) = number of nonzero coordinates; reason: same objects
--   - encoding: determined by its principal moments (every finite simple graph H with H ≡_μ G is isomorphic to G) → H : SimpleGraph (Fin m) for every m; reason: every finite simple graph is isomorphic to one on Fin m, and moments and isomorphism are invariant under relabelling; the empty-word moment forces m = n
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S6.4, p.44 (PDF 45)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_Supplement_IsBinaryObstruction
import Definitions.Def_IntADSat_Supplement_Determined

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Theorem S6.4 (A binary obstruction that certifies rigidity)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.44 (PDF 45)). Suppose `I_G = 2`,
and let `v ∈ {0, 1}^{V(G)}` represent the unique nonzero vector orthogonal modulo `2` to all AD word vectors.
Then `v` has even Hamming weight. If `wt(v) ≡ 2 (mod 4)`, the graph `G` is determined by its principal
moments, although it is not integrally AD-saturated.

**Formalization Note** `I_G = |ℤⁿ/Λ_G| = 2` (`Nat.card`, base convention; it forces AD-fullness). The
existence and uniqueness of `v` asserted by "the unique" is the first conclusion; the others hold for that `v`.
`wt(v)` is the number of nonzero coordinates. -/
theorem theorem_S6_4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hI : Nat.card ((Fin n → ℤ) ⧸ IntADSat.wordLattice G) = 2) :
    (∃! v : Fin n → ZMod 2, IsBinaryObstruction G v) ∧
    ∀ v : Fin n → ZMod 2, IsBinaryObstruction G v →
      Even (Finset.univ.filter fun i => v i ≠ 0).card ∧
      ((Finset.univ.filter fun i => v i ≠ 0).card % 4 = 2 →
        Determined G ∧ IntADSat.wordLattice G ≠ ⊤) := by sorry

end IntADSat.Supplement
