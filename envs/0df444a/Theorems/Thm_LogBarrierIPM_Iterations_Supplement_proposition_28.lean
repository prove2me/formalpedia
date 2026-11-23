-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_proposition_28
-- name    : LogBarrierIPM.Iterations.Supplement.proposition_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:26:05.695795+00:00
-- url     : https://prove2.me/theorems/cff686ce-77dd-4804-945d-d5bca071d116
-- title:
--   Proposition 28 — tube segment bound (corrected: separated endpoints)
-- statement:
--   Assume Assumption 13. Let $a\le b$, let $0<\varepsilon<\varepsilon_0$, and consider $p\ge1$ consecutive tropical segments with arbitrary points $z^0,\ldots,z^p\in\mathbb T^{2N}$. Suppose their union lies in the closed $\varepsilon$-tube around $C^{\rm trop}([a,b])$, and its first and last points lie in the $\varepsilon$-balls of $C^{\rm trop}(a)$ and $C^{\rm trop}(b)$. Suppose also that every vertex parameter $v\in(a,b)$ satisfies
--   $$d_\infty(C^{\rm trop}(a),C^{\rm trop}(v))>2\varepsilon,\qquad d_\infty(C^{\rm trop}(b),C^{\rm trop}(v))>4\varepsilon.$$
--   Then
--   $$p\ge\gamma([a,b]).$$
--   No endpoint is required to be a vertex and the paper's $\varepsilon_0$ is retained. The printed assertion, without the separation, is false: for $n=m=2$, $A=I$, $b=(1,t^2)$, $c=(1,1)$ and small $\eta>0$, one tropical segment meets every printed hypothesis on $[-\eta,\eta]$ although $\gamma([-\eta,\eta])=2$. In the same example neither constant $2$ nor $4$ can be lowered.
--
--   Differences from the source:
--   - correction: ε<ε0 alone gives the count → also every interior vertex is at distance >2ε from the lower endpoint and >4ε from the upper endpoint; reason: without it an endpoint can serve as the witness of a neighbouring vertex; n=m=2, A=I, b=(1,t²), c=(1,1) gives p=1<γ=2, also at distance exactly 2ε below and exactly 4ε above
--   - generalization: N=n+m is the positive number of variables of the dual pair → no hypothesis N≥1; reason: at N=0 the path is constant and γ=1≤p; every instance of the source is included
--   - encoding: a polygonal path and its least positive tropical segment count → p≥1, segments joining C(a) to C(b), and a WithTop natural infimum with empty value +∞; reason: the source uses consecutive segments and positive counts; no sInf-of-empty default yields zero
--   - encoding: ε0, a minimum over pairs of distinct vertices → an extended-real infimum, +∞ with fewer than two vertices; reason: this is the convention min ∅ = +∞
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: the point C^trop(λ) of T^{2N}, indexed from 1 → a real vector indexed by Fin ((n+m)+(n+m)), in the order x, w, s, y; reason: under Assumption 13 all coordinates are finite by (20); Theorem 15 asserts that this vector is the barycenter
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 24, Proposition 28

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalTube

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem proposition_28 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (a b' : ℝ) (hab : a ≤ b')
    (ε : ℝ) (hε : 0 < ε) (hsmall : (ε : EReal) < epsilonZero (tropicalPath A b c))
    (hsep : EndpointsSeparated (tropicalPath A b c) a b' (ε : EReal))
    (p : ℕ) (hp : 1 ≤ p)
    (z : Fin (p + 1) → Fin ((n + m) + (n + m)) → WithBot ℝ)
    (hcontained : tropicalChain p z ⊆ tube (tropicalPath A b c) a b' (ε : EReal))
    (hstart : z 0 ∈ tropicalBall (tropicalizeReal (tropicalPath A b c a)) (ε : EReal))
    (hend : z (Fin.last p) ∈ tropicalBall (tropicalizeReal (tropicalPath A b c b')) (ε : EReal)) :
    gamma (tropicalPath A b c) a b' ≤ (p : WithTop ℕ) := by sorry

end LogBarrierIPM.Iterations.Supplement
