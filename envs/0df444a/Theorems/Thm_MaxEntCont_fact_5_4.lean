-- Prove2me | Theorems.Thm_MaxEntCont_fact_5_4
-- name    : MaxEntCont.fact_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:02.177747+00:00
-- url     : https://prove2.me/theorems/2385e00f-b7e7-4406-b873-aa2d63ed11b1
-- title:
--   Fact 5.4 (Papadopoulou) — stable ⇔ face function lsc ⇔ $x\mapsto\dim F(x)$ lsc
-- statement:
--   Let $C$ be a convex body, i.e. a compact convex subset of a finite-dimensional real normed space, with the subspace topology. Then the following are equivalent:
--
--   1. $C$ is stable, i.e. the mid-point map $C\times C\to C$, $(x,y)\mapsto\frac12(x+y)$, is open;
--   2. the face function $x\mapsto F(x)$ of $C$ is lower semicontinuous;
--   3. the function $C\to\mathbb N_0$, $x\mapsto\dim F(x)$, is lower semicontinuous.
--
--   Here $F(x)$ is the face of $C$ containing $x$ in its relative interior and $\dim$ is the dimension of the affine hull. The equivalence is due to Papadopoulou (Math. Ann. 229, 1977). Since extremal points have dimension zero, (1) and (3) show that in a stable convex body a limit of extremal points is an extremal point.
--
--   **Formalization Note** Stability is `MaxEntCont.IsStable`, (2) is `MaxEntCont.IsLowerSemicontinuousFaceFunction`, and (3) is Mathlib's `LowerSemicontinuousOn` on $C$ for the $\mathbb N$-valued function `MaxEntCont.faceDim C`. All three are stated together as `List.TFAE`.
--
--   Differences from the source:
--   - encoding: all sets lie in a finite-dimensional real normed space (standing assumption, p. 4) → explicit `[FiniteDimensional ℝ X]` binder; reason: the paper's tacit assumption, made explicit
--   - encoding: open subsets of $C$ in the lower semicontinuity of the face function → open subsets $G$ of the ambient space, intersected with $F(x')$; reason: $F(x')\subseteq C$, so $(G\cap C)\cap F(x')=G\cap F(x')$
--   - encoding: $F(x)$ → `minFace C x`; reason: identified with the paper's face function by Fact 5.3
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Fact 5.4, p. 13 (Papadopoulou [34])

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_MaxEntCont_faceDim
import Definitions.Def_MaxEntCont_IsStable
import Definitions.Def_MaxEntCont_IsLowerSemicontinuousFaceFunction

namespace MaxEntCont

/-- **Fact 5.4 (Stable convex bodies)** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Fact 5.4, p. 13; Papadopoulou, Math. Ann. 229
(1977), [34]): "If `C` is a convex body then the following are equivalent: (1) The convex body `C`
is stable. (2) The face function `x ↦ F(x)` of `C` is lower semi-continuous. (3) The function
`C → ℕ₀, x ↦ dim(F(x))` is lower semi-continuous."

**Formalization Note** A convex body is a compact convex set (p. 4) in a finite-dimensional real
normed space (standing assumption, p. 4). Stability is `MaxEntCont.IsStable` (mid-point map open,
(5.2)); lower semicontinuity of the face function is
`MaxEntCont.IsLowerSemicontinuousFaceFunction`; `dim F(x)` is `MaxEntCont.faceDim C x` (dimension
of the affine hull of `F(x) = minFace C x`), and (3) is Mathlib's `LowerSemicontinuousOn` on `C`
for the ℕ-valued function. All three implications are stated (`List.TFAE`). -/
theorem fact_5_4 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (C : Set X) (hCc : IsCompact C) (hCv : Convex ℝ C) :
    List.TFAE [IsStable C, IsLowerSemicontinuousFaceFunction C,
      LowerSemicontinuousOn (fun x => faceDim C x) C] := by sorry

end MaxEntCont
