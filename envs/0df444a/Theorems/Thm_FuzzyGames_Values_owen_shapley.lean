-- Prove2me | Theorems.Thm_FuzzyGames_Values_owen_shapley
-- name    : FuzzyGames.Values.owen_shapley
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:55.238745+00:00
-- url     : https://prove2.me/theorems/978dde26-5a7c-412f-994f-e03763f27441
-- title:
--   Remark 8.2, (7)–(8) — the diagonal value of Owen's multilinear extension is the Shapley value
-- statement:
--   Let $f$ be a coalitional worth function defined on all coalitions $A\subseteq N$, with $f(\emptyset)=0$, and let
--   $$xv(\tau)=\sum_{A\subseteq N} f(A)\prod_{i\in A}\tau_i\prod_{j\notin A}(1-\tau_j)$$
--   be its Owen multilinear extension. Then $xv\in V^n$ and the diagonal formula (4) applied to $xv$ is the Shapley value (7) of $f$:
--   $$(\psi_n\, xv)_i=\sum_{A\ni i}\frac{(|A|-1)!\,(n-|A|)!}{n!}\bigl(f(A)-f(A\setminus\{i\})\bigr).$$
--
--   This connects the value of smooth fuzzy games with the classical value of games with side payments.
--
--   **Formalization Note** Formula (7) uses $f(A\setminus\{i\})$ for every coalition, so the family $\mathcal C$ of Remark 8.2 is taken to be all coalitions, with $f(\emptyset)=0$ (the paper's convention $v(\emptyset)=0$), which is what places $xv$ in $V^n$. The Shapley value is the published definition `Supermodularity.Cooperative.ShapleyValue`, whose formula $\sum_{S\subseteq N\setminus\{i\}}\frac{|S|!(n-|S|-1)!}{n!}(f(S\cup\{i\})-f(S))$ is (7) re-indexed by $S=A\setminus\{i\}$. The Cornet extension of the same remark is not stated, because it is not $C^1$ on the boundary of the cube.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, Remark 8.2, (7) and (8), p. 11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

namespace FuzzyGames.Values

/-- Remark 8.2, (7)–(8) (p. 11): for a coalitional worth function `f` on all coalitions with
`f(∅) = 0`, Owen's multilinear extension `xv` lies in `V^n`, and the diagonal value (4) of
`xv` is the Shapley value of `f`. -/
theorem owen_shapley (n : ℕ) (f : Finset (Fin n) → ℝ) (hf : f ∅ = 0) :
    owenExtension f ∈ Vn n ∧
      diagValue (owenExtension f) = Supermodularity.Cooperative.ShapleyValue f := by sorry

end FuzzyGames.Values
