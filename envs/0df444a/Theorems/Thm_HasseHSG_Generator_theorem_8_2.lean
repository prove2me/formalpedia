-- Prove2me | Theorems.Thm_HasseHSG_Generator_theorem_8_2
-- name    : HasseHSG.Generator.theorem_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:47.44348+00:00
-- url     : https://prove2.me/theorems/9c8452d6-5990-46de-92da-69d0f00d10ac
-- title:
--   Theorem 8.2 — $f\circ p\not\equiv0\bmod t^B$ for nonzero $f$ with $\deg f\le d$, $\dim\hat\partial^*f=r$
-- statement:
--   Let $F$ be an arbitrary field, let $a_1,\dots,a_n\in F$ be distinct and nonzero, and let $q$ be transcendental over $F$. Let $f\in F[x_1,\dots,x_n]$ be a nonzero polynomial of total degree at most $d$ with $\dim_F\hat\partial^*f=r$. Let $p=(p_1,\dots,p_n)$ with $p_i(t)=\sum_{m\ge1}(a_it)^m/[m]_q$. Then
--
--   $$f\circ p\not\equiv0\pmod{t^B}\quad\text{in }F(q)[[t]],\qquad B=(nd-1)\binom r2+r.$$
--
--   Truncating each $p_i$ below degree $B$ therefore gives a nonzero-preserving map over $F(q)$ for the class of polynomials with $\dim\hat\partial^*f=r$.
--
--   **Formalization Note.** $f\in F[x]$ is viewed in $F(q)[t,x]$ before composing with $p$. $\dim$ is `Module.rank` (a cardinal). $t^B$ uses `(Bnum n d r).toNat`. $B\ge0$ always holds here: $f\neq0$ gives $r\ge1$, and when $nd=0$ the polynomial $f$ is constant, so $r=1$ and $B=1$.
--
--   Differences from the source:
--   - encoding: t^B with B ∈ ℤ → PowerSeries.X ^ (Bnum n d r).toNat; reason: B ≥ 0 under the hypotheses (f ≠ 0 ⇒ r ≥ 1; nd = 0 ⇒ r = 1), so toNat changes nothing
--   - encoding: dim ∂̂*f = r → Module.rank F (hasseSpace f) = r; reason: cardinal dimension
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 36, Theorem 8.2

import Mathlib
import Definitions.Def_HasseHSG_Generator_HasseSpace
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QLogCurve

namespace HasseHSG.Generator

/-- Theorem 8.2 (p. 36): for a nonzero `f ∈ F[x]` of degree at most `d` with `dim ∂̂* f = r`,
`f ∘ p ≢ 0 mod t^B` in `F(q)[[t]]`. -/
theorem theorem_8_2 {F : Type*} [Field F] {n d r : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : MvPolynomial (Fin n) F) (hf0 : f ≠ 0) (hf : f.totalDegree ≤ d)
    (hr : Module.rank F (hasseSpace f) = r) :
    ¬ PowerSeries.X ^ (Bnum n d r).toNat ∣
      compP a (MvPolynomial.map (algebraMap F (Polynomial (Fq F))) f) := by sorry

end HasseHSG.Generator
