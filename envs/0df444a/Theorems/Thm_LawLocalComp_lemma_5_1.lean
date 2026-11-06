-- Prove2me | Theorems.Thm_LawLocalComp_lemma_5_1
-- name    : LawLocalComp.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:32.15589+00:00
-- url     : https://prove2.me/theorems/28f475e2-f203-4f2e-8618-c730758637bd
-- title:
--   Lemma 5.1 (Moving-constant calibration)
-- statement:
--   Let $\Phi$ satisfy the robust comparison (14),
--   $$(1+\varepsilon)^{-1}\mathbb E\|L\|_\infty\le\mathbb E\|\tilde L\|_\infty\le(1+\varepsilon)\mathbb E\|L\|_\infty,$$
--   for every admitted selection of a lower contract (a resource with $M\ge2$, on an input class containing the rational point masses). For rational $t\ge0$, the output $B_t=\Phi(\delta_t)$ of the constant input $t$ satisfies
--   $$\mathbb E|B_t-t|\le5\varepsilon t.\tag{15}$$
--   Outputs of constant inputs need not stay constant; this calibration bounds how far they move.
--
--   Differences from the source:
--   - generalization: rational ε and either lower contract → every real ε > 0, every resource with M ≥ 2 and every input class containing the rational point masses; reason: both lower contracts (horizon N ≥ 2, rank q ≥ 2) and the structured ones are instances; the proof uses only the singleton and two-copy constant selections, which these admit
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 5.1, (15), p.8, under (14), p.8

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_dirac
import Definitions.Def_LawLocalComp_Resource_M

namespace LawLocalComp

/-- **Lemma 5.1 (Moving-constant calibration).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 5.1, (15), p.8, under the robust comparison (14), p.8.

Let `Φ` satisfy (14) with `κ = 1 + ε` under a lower contract (a resource with `M ≥ 2`, on a class of
inputs containing the rational point masses). For rational `t ≥ 0`, the output `B_t = Φ(δ_t)` of the
constant input `t` satisfies `E|B_t − t| ≤ 5εt`.

**Formalization Note.** Any resource with `M ≥ 2` admits the singleton and the two-copy selections
the proof uses, so this covers both lower contracts (horizon and rank) and the structured ones. -/
theorem lemma_5_1 (ε : ℝ) (hε : 0 < ε) (Φ : Law → Law) (R : Resource) (hR : 2 ≤ R.M)
    (cls : Law → Prop) (hcls : ∀ t : ℚ, 0 ≤ t → cls (dirac t))
    (hΦ : RobustContract Φ R cls (1 + ε)) (t : ℚ) (ht : 0 ≤ t) :
    ∑ y ∈ (Φ (dirac t)).w.support, (Φ (dirac t)).w y * |y - t| ≤ 5 * ε * t := by sorry

end LawLocalComp
