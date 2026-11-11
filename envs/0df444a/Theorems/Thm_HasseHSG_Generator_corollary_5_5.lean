-- Prove2me | Theorems.Thm_HasseHSG_Generator_corollary_5_5
-- name    : HasseHSG.Generator.corollary_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:39.827395+00:00
-- url     : https://prove2.me/theorems/062fbfa3-5187-46d9-aeb3-098b3ce11d80
-- title:
--   Corollary 5.5 — if $f\circ p\equiv0 \bmod t^B$ then $D^i_{q,d}(f)\circ p\equiv0\bmod t^{B-i}$ for $0\le i\le B$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $p$ be the $q$-logarithmic curve of Eq. (15).
--
--   Let $B$ be a nonnegative integer and $f\in F(q)[t,x]$ with $\deg_x f\le d$ and $f\circ p\equiv0\pmod{t^B}$. Then
--
--   $$D^i_{q,d}(f)\circ p\equiv0\pmod{t^{B-i}}\qquad\text{for every }0\le i\le B.$$
--
--   Each application of $D_{q,d}$ lowers the order of vanishing of $f\circ p$ at $t=0$ by at most one. This is the step that turns "$f\circ p$ vanishes to high order" into a contradiction with a nonzero Wronskian of low $t$-degree (Theorem 8.2).
--
--   **Formalization Note.** $h\equiv0\pmod{t^B}$ is $t^B\mid h$ in $F(q)[[t]]$. $D^i_{q,d}$ is the $i$-fold iterate of `DqdPoly`.
--
--   Differences from the source:
--   - encoding: h = 0 mod t^B in F(q)[[t]] → PowerSeries.X ^ B ∣ h; reason: same condition
--   - encoding: D^i_{q,d}(f), iterates of a polynomial operator → (DqdPoly a d)^[i] f; reason: Lemma 5.2 keeps the iterates in the domain deg_x ≤ d
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 24, Corollary 5.5

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QLogCurve

namespace HasseHSG.Generator

/-- Corollary 5.5 (p. 24). -/
theorem corollary_5_5 {F : Type*} [Field F] {n d : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (B : ℕ) (f : PolyQT F n) (hf : f.totalDegree ≤ d)
    (hB : PowerSeries.X ^ B ∣ compP a f) :
    ∀ i ≤ B, PowerSeries.X ^ (B - i) ∣ compP a ((DqdPoly a d)^[i] f) := by sorry

end HasseHSG.Generator
