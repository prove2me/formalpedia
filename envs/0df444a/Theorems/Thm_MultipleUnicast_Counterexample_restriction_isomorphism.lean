-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_restriction_isomorphism
-- name    : MultipleUnicast.Counterexample.restriction_isomorphism
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:11.39292+00:00
-- url     : https://prove2.me/theorems/166b508c-9ff8-465d-ac18-25c741ad0424
-- title:
--   Section 4, unnumbered W_C isomorphism — restriction and causal computation
-- statement:
--   Let $W_C=\{w\in W:w|_C=0\}$, and let $x\in\mathbb F_9^B$ be any input tuple. The linear restriction map is bijective:
--   $$\operatorname{restriction}:W_C\longrightarrow\mathbb F_9^B,\qquad w\longmapsto w|_B.$$
--   Every vertex has five available positions, their interpolation is a linear inverse to evaluation, and for every $x$ there is a unique $w\in W_C$ whose restriction is $x$ and whose full edge assignment equals the recursively computed execution on $x$.
--
--   This states both the specified isomorphism and the computation claim, rather than an unrelated abstract isomorphism. All tuples are allowed; no compatible extension is assumed.
--
--   Differences from the source:
--   - encoding: local incident vectors and restriction W_C → F9^B → masked local linear maps, submodule preimages, and the literal coordinate restriction; reason: zero masking outside an incident set adds no local condition
--   - encoding: the unique local interpolation and its causal computation → classical solving with a zero off-domain default, plus solvability, linearity and computation as conclusions; reason: uniqueness on every available input eliminates the total-function fallback on all executions
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, unnumbered W_C ≅ F^157 display and following sentence, PDF p. 12 / printed p. 11; local rule on PDF p. 11 / printed p. 10

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- §4: the isomorphism is restriction itself, and the causal interpolation computes it. -/
theorem restriction_isomorphism :
    Function.Bijective restriction ∧ LocalInterpolation ∧
    ∀ x : Input, ∃! w : WC,
      restriction w = x ∧ execution x = w.val := by sorry

end MultipleUnicast.Counterexample
