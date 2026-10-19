-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_Model_chi_gt_bot
-- name    : OAI.FiniteEntropySeparation.Model.chi_gt_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:09:22.148989+00:00
-- url     : https://prove2.me/theorems/ab5a49dc-7481-4193-abfd-47e3729434da
-- title:
--   The microstates free entropy of OpenAI's model tuple X_p(h) is finite from below (χ > −∞) for p ≥ 2, h > 0 (OpenAI finite-entropy separation)
-- statement:
--   **The model** (definitions bundle `OAIQWFE000` of this split). For $p \in \mathbb N$ with $p \ne 0$ (`[NeZero p]`), `Model.H p` is OpenAI's Hilbert space `FreeTensor.Space (Fin p) (Fin ((p+1)+(p+1))) (Multiplicative (ZMod p))`, a Fock-type space with semicircular, noise and group generators. `Model.M p` is its von Neumann algebra `FreeTensor.algebra …`, and `Model.τ p` is the vacuum tracial vector `FreeTensor.tracialVector …`. `Model.C p` is the $(p+1)$-tuple whose first $p$ entries are the semicircular operators `semicircularB i` and whose last entry is `equidiscreteSignal p`. For $h \in \mathbb R$, `Model.X p h` $=$ `heatTuple (C p) (initialNoise p) h`, i.e. $X_i = C_i + \sqrt h\,S_i$ (`Real.sqrt`), where the noise $S_i = $ `initialNoise p i` is the semicircular operator `semicircularN` on the $i$-th of the first $p+1$ noise labels.
--
--   **Microstates free entropy** (published bundle `Def_FiniteEntropySeparation`). For a tracial vector $\tau$ and an $n$-tuple $X$, `microstates τ X R m d ε` is the set of $n$-tuples of $d \times d$ Hermitian matrices (`MatrixCoordinates n d`, read through `hermitianMatrix`) with operator norms at most $R$ whose normalized trace moments of all words of length at most $m$ are within $\varepsilon$ of the moments `wordMoment τ X w`. `chiCutoff τ X R` is
--   $$\inf_{m}\ \inf_{\varepsilon > 0}\ \limsup_{d \to \infty} \Bigl(\frac{1}{(d+1)^2}\log \mathrm{vol}\bigl(\mathrm{microstates}\ \tau\ X\ R\ m\ (d+1)\ \varepsilon\bigr) + \frac{n}{2}\log(d+1)\Bigr)$$
--   in the extended reals (`EReal`, with `ENNReal.log` of the Lebesgue volume), and `chi τ X` $= \sup_{R > 0}$ `chiCutoff τ X R`.
--
--   **Statement.** Let $p \ge 2$ and $h > 0$. Then $\bot < $ `chi (τ p) (X p h)` in `EReal`, i.e. the microstates free entropy of the tuple `Model.X p h` is not $-\infty$.
--
--   Lean: `OAI.FiniteEntropySeparation.Model.chi_gt_bot`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/MicrostatesLower.lean`). `chi`, `chiCutoff`, `microstates`, `hermitianMatrix`, `matrixOpNorm`, `matrixMoment`, `wordMoment`, `heatTuple` and `MatrixCoordinates` come from the published bundle `Def_FiniteEntropySeparation`; `Model.H`, `Model.M`, `Model.τ`, `Model.C`, `Model.X`, `Model.initialNoise` and the operators they use from the definitions bundle `OAIQWFE000` of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/MicrostatesLower.lean (declaration OAI.FiniteEntropySeparation.Model.chi_gt_bot)

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 namespace Model
 theorem chi_gt_bot (p : ℕ) [NeZero p] (hp : 2≤p) {h : ℝ} (hh : 0<h) :
    (⊥:EReal)<chi (τ p) (X p h) := by
  sorry
 end Model
end FiniteEntropySeparation

end

end OAI
end
