-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SpectralDimension_spectral_effective_bound
-- name    : OAI.PermanentBorder.SpectralDimension.spectral_effective_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:57:33.94698+00:00
-- url     : https://prove2.me/theorems/ebe17738-78c8-445a-9e97-a402ee1ea844
-- title:
--   A transcendence-degree bound for the spectral curve of a diagonal pencil in characteristic two (OpenAI permanent)
-- statement:
--   **Notation** (definitions bundle `OAIQWPB000` of this split). For $\theta \in L^{k+1}$ and a matrix $A$ over $L$, the pencil is $P(x) = x\,\mathrm{diag}(\theta) + A$ (`pencilBase`), and its spectral curve is $\det\bigl(y I + P(x)\bigr) \in L[x][y]$ (`pencilMatrix`). `curveCoefficientField` of a bivariate polynomial is the field generated over $K$ by its coefficients. The normalization defect (`normalizationDefect θ A`) is the length, as an $L$-module, of the quotient of the integral closure of $L[x]$ in $L(x)[y]/(\chi)$ by the image of $L[x][y]/(\chi)$, where $\chi$ is the characteristic polynomial of $-P$.
--
--   **The statement.** Let $K \subseteq L$ be fields of characteristic $2$, $K$ infinite and perfect, $L$ algebraically closed, and $k + 1 \ge 4$. Let $\theta \in K^{k+1}$ have distinct entries, let $A$ be a $(k+1) \times (k+1)$ matrix over $L$, and let $T$ be a natural number at most the normalization defect of $(\theta, A)$. Then there is $n$ such that the coefficient field of the spectral curve has transcendence degree at most $n$ over $K$, and
--   $$18n + T \;\le\; 9(k+1)(k+2).$$
--
--   Lean: `OAI.PermanentBorder.SpectralDimension.spectral_effective_bound`, OpenAI's theorem of that name (in `lean/OAI/Algebra/Determinantal/Main.lean`).
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf, Sections 4–6; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Determinantal/Main.lean (declaration OAI.PermanentBorder.SpectralDimension.spectral_effective_bound)

import Mathlib
import Definitions.Def_OAIQWPB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers SpectralPlane FrobeniusPlane CurveFamily
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

variable [CharP K 2] [CharP L 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem spectral_effective_bound {k : ℕ} (hk : 4 ≤ k+1)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (T : ℕ)
    (hT : (T : ℕ∞) ≤ normalizationDefect (fun i => algebraMap K L (θ i)) A) :
    ∃ n : ℕ, Algebra.trdeg K (curveCoefficientField (K := K)
      (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det) ≤ (n : Cardinal) ∧
      18*n+T ≤ 9*((k+1)*(k+2)) := by
  sorry

end PermanentBorder.SpectralDimension

end OAI
end
