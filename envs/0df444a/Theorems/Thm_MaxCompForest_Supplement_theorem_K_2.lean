-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_K_2
-- name    : MaxCompForest.Supplement.theorem_K_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:30:48.340644+00:00
-- url     : https://prove2.me/theorems/bdbc3d37-747b-4b5b-a74c-5b4dda39ab0c
-- title:
--   Theorem K.2 — independent averaging has a logarithmic penalty on the $h$-cube
-- statement:
--   For every integer $q\ge16$ and $\sigma>0$ set
--   $$h=8\lfloor\log_2q\rfloor,\qquad n=2^h,\qquad\gamma=\frac1{50},\qquad R^2=q\sigma^2\gamma .$$
--   On the unit-conductance $h$-cube, $D=hI$, $n>q^2$ and $\lambda_{q+1}(N)\ge\gamma$, and for every $1\le b\le q^2$
--   $$R_{\mathrm{part},b}\ge\frac{R^2h}{4},\qquad R^*\le2q\sigma^2,\qquad\frac{R_{\mathrm{part},b}}{R^*}\ge\frac{h}{400}\ge\frac{3}{200}\log_2q,\tag{K.2}$$
--   where $R^*$ is the minimax risk of the Gaussian model (5.2) over $H_R=\{f:f^{\top}Lf\le R^2\}$ and $R_{\mathrm{part},b}$ the best worst-case risk of block averaging under a partition law with at most $b$ blocks drawn independently of the signal and observations. In particular this includes $b=2q$ and any fixed linear budget $b=\lfloor cq\rfloor$ for large $q$: the logarithmic loss of Theorem 5.2 cannot be removed for independent block averages.
--
--   **Formalization Note** Vertices of the cube are `Fin h → Bool`; $R=\sqrt{q\sigma^2/50}$. The ratio is division in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: {−1,1}^h, n = 2^h → Fin h → Bool, n = Fintype.card (Fin h → Bool); reason: the same graph
--   - encoding: R² = qσ²γ → R = √(qσ²/50); reason: R ≥ 0, so R² = qσ²/50
--   - encoding: R_part,b/R* ≥ h/400 → ofReal(h/400) ≤ R_part,b / R* in ℝ≥0∞; reason: risks are in ℝ≥0∞; R* is finite and positive here
--   - encoding: "In particular this includes b = 2q and … b = ⌊cq⌋" → covered by the clause for every 1 ≤ b ≤ q²; reason: these budgets lie in the range for large q
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem K.2 and (K.2), p.62 (PDF p.64)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_Supplement_cube
import Definitions.Def_MaxCompForest_Supplement_minimaxRisk
import Definitions.Def_MaxCompForest_Supplement_partRisk
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem K.2 (Independent averaging has a logarithmic penalty).** For every integer `q ≥ 16` and `σ > 0`, set
`h = 8⌊log₂ q⌋`, `n = 2^h`, `γ = 1/50`, `R² = qσ²γ`. On the unit-conductance `h`-cube, `D = hI`, `n > q²` and
`λ_{q+1}(N) ≥ γ`; and for every `1 ≤ b ≤ q²`, `R_part,b ≥ R²h/4`, `R* ≤ 2qσ²`, and
`R_part,b/R* ≥ h/400 ≥ (3/200) log₂ q` (K.2).

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem K.2 and (K.2), p.62.

**Formalization Note.** `⌊log₂ q⌋` is `Nat.log 2 q`; the cube is `cube h` on `Fin h → Bool`, so `n` is
`Fintype.card (Fin h → Bool) = 2^h`. `R = √(qσ²/50)`, so `R² = qσ²γ`. Risks are in `ℝ≥0∞` and the ratio is
`ℝ≥0∞` division. The "In particular" sentence of the theorem is the case `b = 2q` or `b = ⌊cq⌋` of the `∀ b` clause. -/
theorem theorem_K_2 (q : ℕ) (σ : ℝ) (hq : 16 ≤ q) (hσ : 0 < σ) :
    (∀ v, MaxCompForest.deg (cube (8 * Nat.log 2 q)) v = (8 * Nat.log 2 q : ℕ)) ∧
    q ^ 2 < Fintype.card (Fin (8 * Nat.log 2 q) → Bool) ∧
    (1 / 50 : ℝ) ≤ MaxCompForest.lam (cube (8 * Nat.log 2 q)) (MaxCompForest.deg (cube (8 * Nat.log 2 q))) q ∧
    ∀ b : ℕ, 1 ≤ b → b ≤ q ^ 2 →
      ENNReal.ofReal (Real.sqrt (q * σ ^ 2 / 50) ^ 2 * (8 * Nat.log 2 q : ℕ) / 4) ≤
          partRisk (cube (8 * Nat.log 2 q)) σ (Real.sqrt (q * σ ^ 2 / 50)) b ∧
      minimaxRisk (cube (8 * Nat.log 2 q)) σ (Real.sqrt (q * σ ^ 2 / 50)) ≤ ENNReal.ofReal (2 * q * σ ^ 2) ∧
      ENNReal.ofReal (((8 * Nat.log 2 q : ℕ) : ℝ) / 400) ≤
          partRisk (cube (8 * Nat.log 2 q)) σ (Real.sqrt (q * σ ^ 2 / 50)) b /
            minimaxRisk (cube (8 * Nat.log 2 q)) σ (Real.sqrt (q * σ ^ 2 / 50)) ∧
      3 / 200 * Real.logb 2 q ≤ ((8 * Nat.log 2 q : ℕ) : ℝ) / 400 := by sorry

end MaxCompForest.Supplement
