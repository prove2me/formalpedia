-- Prove2me | Theorems.Thm_KingmanSubadditive_BanachAlgebra_logNormProcess_conditions
-- name    : KingmanSubadditive.BanachAlgebra.logNormProcess_conditions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:22.164978+00:00
-- url     : https://prove2.me/theorems/80cc8314-dc7a-4b6a-80ab-7236e7e5f74d
-- title:
--   Proof of Theorem 6, p. 893 — x_st = log‖Y_{s+1}⋯Y_t‖ satisfies S₁, S₂ and S₃′
-- statement:
--   Let $\mathfrak B$ be a real or complex Banach algebra, so that $\|AB\|\le\|A\|\,\|B\|$ (2.3.2). Let $(Y_n)_{n\ge1}$ be a stationary sequence of $\mathfrak B$-valued random elements with
--   $$E\{(\log\|Y_1\|)^+\}<\infty .$$
--   Define, for nonnegative integers $s<t$,
--   $$x_{st}=\log\|Y_{s+1}Y_{s+2}\cdots Y_t\|\in[-\infty,\infty).$$
--   Then every $x_{st}$ is a random variable, and $x=(x_{st})$ satisfies
--
--   1. **S₁**: $x_{su}\le x_{st}+x_{tu}$ for all $s<t<u$ and every sample point;
--   2. **S₂**: the joint distributions of $(x_{s+1,t+1})$ are the same as those of $(x_{st})$;
--   3. **S₃′**: $E(x_{01}^+)<\infty$.
--
--   This is the reduction in the proof of Theorem 6: once the log-norm process is known to satisfy S₁, S₂ and S₃′, Theorems 1 and 2 give the limit of $n^{-1}\log\|Y_1\cdots Y_n\|$.
--
--   **Formalization Note** The logarithm is extended-real valued, $\log\|0\|=-\infty$, and S₁ is read in $[-\infty,\infty]$ with $-\infty+a=-\infty$. Each $Y_n$ is strongly measurable (a pointwise limit of simple functions), which makes the products measurable without assuming $\mathfrak B$ separable. $\mathfrak B$ is a complete unital normed ring that is a normed algebra over $\mathbb R$ or $\mathbb C$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 893, §2.3, proof of Theorem 6, (2.3.2)

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process
import Definitions.Def_KingmanSubadditive_BanachAlgebra_RandomProduct

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **Proof of Theorem 6, §2.3, p. 893** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "If `x_st = log ‖Y_{s+1} Y_{s+2} ⋯ Y_t‖`,
then (2.3.2) implies that `x = (x_st)` satisfies S₁, S₂ and S₃′." Here `(Y_n)_{n≥1}` is a
stationary sequence in a real or complex Banach algebra `𝔅` with `E{(log ‖Y₁‖)⁺} < ∞` (the
hypotheses of Theorem 6), and (2.3.2) is `‖AB‖ ≤ ‖A‖ ‖B‖`.

The conclusion lists: every `x_st` (`s < t`) is measurable; S₁ holds for every `ω` (in `EReal`);
S₂ holds (equality of the laws of the shifted and unshifted paths on `Interval → EReal`); and
S₃′ holds in the form `E(x₀₁⁺) < ∞`.

**Formalization Note.** `x_st` takes values in `[−∞, ∞)`: `log ‖0‖ = −∞` (`ENNReal.log 0 = ⊥`),
so the process is `EReal`-valued and S₁ is read with `−∞ + a = −∞`. The paper's Theorem 2 is
stated for real random variables; the paper applies it to this process without comment. Each
`Y_n` is strongly measurable (separably valued), which makes the products measurable without
assuming `𝔅` separable. `𝔅` is a unital `NormedRing` (`‖AB‖ ≤ ‖A‖‖B‖` is part of the structure)
that is complete and a normed algebra over `𝕜 = ℝ` or `ℂ` (`RCLike`). -/
theorem logNormProcess_conditions {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    IsMeasurableFamily (logNormProcess Y) ∧
      (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
        logNormProcess Y s u ω ≤ logNormProcess Y s t ω + logNormProcess Y t u ω) ∧
      S2 P (logNormProcess Y) ∧
      ∫⁻ ω, (logNormProcess Y 0 1 ω).toENNReal ∂P < ⊤ := by sorry

end KingmanSubadditive.BanachAlgebra
