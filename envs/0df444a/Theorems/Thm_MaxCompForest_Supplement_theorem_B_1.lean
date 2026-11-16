-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_B_1
-- name    : MaxCompForest.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:29:10.383063+00:00
-- url     : https://prove2.me/theorems/65d564d3-7825-4ac3-b3e5-86e9da9b12fc
-- title:
--   Theorem B.1 — sharpness at the $2q$-row budget: $\gamma\,\mathrm{OPT}/E\ge\min\{d,\ln(q+1)\}/1280$ (rows) and $/2560$ (real centers)
-- statement:
--   For every pair of integers $q,d\ge1$ there is a finite connected simple graph $G$ with positive rational conductances and more than $2q$ vertices, and a map $\Phi:V(G)\to\mathbb R^d$ with rational coordinates, such that, with $\gamma=1/100$, $\lambda_{q+1}(D^{-1/2}L_GD^{-1/2})\ge\gamma$, $E_G(\Phi)>0$ and
--   $$\frac{\gamma\,\mathrm{OPT}^{\mathrm{row}}_{2q}(\Phi;D)}{E_G(\Phi)}\ \ge\ \frac{\min\{d,\ln(q+1)\}}{1280},\qquad \frac{\gamma\,\mathrm{OPT}^{\mathrm{real}}_{2q}(\Phi;D)}{E_G(\Phi)}\ \ge\ \frac{\min\{d,\ln(q+1)\}}{2560}.$$
--   Here the weights are the actual degrees $d_v$, $E_G(\Phi)=\sum_{uv}c_{uv}\|\Phi_u-\Phi_v\|^2$, $\mathrm{OPT}^{\mathrm{row}}_{2q}$ uses at most $2q$ original rows and $\mathrm{OPT}^{\mathrm{real}}_{2q}$ at most $2q$ arbitrary centers. Both the feature dimension and the spectral index are thus necessary in the quantization coefficient of Theorem 2.1, even with one fixed positive spectral threshold.
--
--   **Formalization Note** The graph is an explicit rational input (loopless, positive rational conductances), required connected and simple; $\Phi$ is the column map of a rational $d\times n$ matrix. $E_G(\Phi)>0$ is part of the conclusion, so the ratios are not vacuous.
--
--   Differences from the source:
--   - encoding: γ·OPTrow_{2q}(Φ; D)/E_G(Φ) ≥ X → E_G(Φ) > 0 and X ≤ (1/100)·rowCost(C)/E_G(Φ) for every nonempty row set C with |C| ≤ 2q; reason: OPTrow is the minimum over these sets; the positive energy is stated so that the ratio is meaningful
--   - encoding: a finite connected simple graph with positive rational conductances; a rational-coordinate map → an explicit RInst, connected and simple; the column map of a rational d × n matrix; reason: the same objects
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem B.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_rowCost
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_energy
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_Supplement_optReal
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem B.1 (Sharpness at the 2q-row budget).** For every pair of integers `q, d ≥ 1` there is a finite connected
simple graph `G` with positive rational conductances, more than `2q` vertices, and a rational-coordinate map
`Φ : V(G) → ℝ^d` such that, with `γ = 1/100`, `λ_{q+1} ≥ γ`,
`γ OPTrow_{2q}(Φ; D)/E_G(Φ) ≥ min{d, ln(q+1)}/1280` and `γ OPTreal_{2q}(Φ; D)/E_G(Φ) ≥ min{d, ln(q+1)}/2560`.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem B.1, p.33.

**Formalization Note.** The graph is an explicit rational input (`RInst`, loopless with positive rational
conductances), required connected and simple. `Φ` is the column map of a rational `d × n` matrix. The ratio is
stated with `E_G(Φ) > 0` asserted, so it is not vacuous. `OPTrow_{2q} ≥ X` is a bound against every nonempty row set of
size at most `2q`; `OPTreal` is the published-style infimum `optReal` with degree weights. -/
theorem theorem_B_1 (q d : ℕ) (hq : 1 ≤ q) (hd : 1 ≤ d) :
    ∃ (I : MaxCompForest.RInst) (x : Fin d → Fin I.n → ℚ),
      I.graph.IsConnected ∧ I.graph.IsSimple ∧ 2 * q < I.n ∧
      (1 / 100 : ℝ) ≤ MaxCompForest.lam I.graph (MaxCompForest.deg I.graph) q ∧
      0 < MaxCompForest.energy I.graph (MaxCompForest.ratFeat x) ∧
      (∀ (Cs : Finset (Fin I.n)) (hC : Cs.Nonempty), Cs.card ≤ 2 * q →
        min (d : ℝ) (Real.log ((q : ℝ) + 1)) / 1280 ≤
          (1 / 100 : ℝ) * MaxCompForest.rowCost (MaxCompForest.deg I.graph)
              (MaxCompForest.rowDist (MaxCompForest.ratFeat x)) Cs hC /
            MaxCompForest.energy I.graph (MaxCompForest.ratFeat x)) ∧
      min (d : ℝ) (Real.log ((q : ℝ) + 1)) / 2560 ≤
        (1 / 100 : ℝ) * optReal (MaxCompForest.deg I.graph) (MaxCompForest.ratFeat x) (2 * q) /
          MaxCompForest.energy I.graph (MaxCompForest.ratFeat x) := by sorry

end MaxCompForest.Supplement
