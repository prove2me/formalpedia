-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_affineSubtract_readable
-- name    : FunctionalInequalities.Analysis.legendre_affineSubtract_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:44.197252+00:00
-- url     : https://prove2.me/theorems/86cc89dc-153b-4ec4-a574-1e72902d9a9b
-- title:
--   Legendre Transform Under Affine Subtraction
-- statement:
--   This gives the exact conjugation formula for subtracting an affine function.
--
--   Let $f:E\to\overline{\mathbb R}$, $a,y\in E$, and $b\in\mathbb R$. For the definition `affineSubtract f a b`, namely
--
--   $$
--   (\operatorname{affineSubtract} f\ a\ b)(x)=f(x)-\bigl(\langle a,x\rangle+b\bigr),
--   $$
--
--   one has
--
--   $$
--   \operatorname{Leg}(\operatorname{affineSubtract}(f,a,b))(y)
--   =
--   \operatorname{Leg}(f)(y+a)+b.
--   $$
--
--   The equality is in `EReal` and remains valid with infinite input or conjugate values.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_affineSubtract (f : E → EReal) (a : E) (b : ℝ) (y : E) :
--       legendre (affineSubtract f a b) y = legendre f (y + a) + (b : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Next: [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9).
--
--   [Source excerpt, lines 40–41](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L40-L41) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L39-L59 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.legendre_affineSubtract`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_affineSubtract_readable (f : E → EReal) (a : E) (b : ℝ) (y : E) :
    legendre (affineSubtract f a b) y = legendre f (y + a) + (b : EReal) := by sorry
