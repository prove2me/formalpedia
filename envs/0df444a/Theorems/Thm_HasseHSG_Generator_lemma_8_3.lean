-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_8_3
-- name    : HasseHSG.Generator.lemma_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:49.592384+00:00
-- url     : https://prove2.me/theorems/022dfbf6-0f05-4957-af69-51d1d783f783
-- title:
--   Lemma 8.3 — if $W(q_0,t)\neq0$ then $f\circ p_{q_0}\not\equiv0\bmod t^B$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   Let $f\in F[x_1,\dots,x_n]$ with $\deg f\le d$ and $\dim\hat\partial^*f=r$. Let $g_1,\dots,g_r\in F[x]$ be a basis of $\hat\partial^*f$ with $g_r=f$, and let $W=W_{D_{q,d}}(g_1,\dots,g_r)\in F[q][t]$ (by Lemma 8.1). Let $q_0\in F$ with $q_0^m\neq1$ for $1\le m\le B-1$, and let $W(q_0,t)$ be $W$ with $q=q_0$ substituted. If $W(q_0,t)\neq0$, then
--
--   $$f\circ p_{q_0}\not\equiv0\pmod{t^B}\quad\text{in }F[t],\qquad p_{q_0,i}(t)=\sum_{m=1}^{B-1}\frac{(a_it)^m}{[m]_{q_0}}.$$
--
--   Every nonzero $f$ in the class therefore survives the truncated curve $p_{q_0}$ for all but at most $R$ values of $q_0$. Interpolating these curves over $R+1$ admissible values of $q_0$ gives the generator of Theorem 1.2.
--
--   **Formalization Note.**
--   - The basis is `Module.Basis (Fin r)`, so $r=\dim\hat\partial^*f$.
--   - $g_r=f$ is the basis vector of index $r-1$; this needs $r\ge1$, which the existence of $g_r$ presupposes.
--   - $W$ is given as $w\in(F[q])[t]$ whose image in $L$ is the Wronskian.
--   - $W(q_0,t)$ is $w$ with every coefficient evaluated at $q_0$.
--   - $t^B$ uses `(Bnum n d r).toNat`; here $B\ge1$.
--
--   Differences from the source:
--   - encoding: g_r = f for a basis g_1, …, g_r → 0 < r and the basis vector of index r − 1 equals f; reason: 0-based indexing; the existence of g_r presupposes r ≥ 1
--   - encoding: W ∈ F[q][t] by Lemma 8.1; W(q₀, t) → a polynomial w : (F[q])[t] with image W in L; w.map (evalRingHom q₀); reason: w is unique since F[q][t] → L is injective
--   - encoding: t^B with B ∈ ℤ → Polynomial.X ^ (Bnum n d r).toNat; reason: B ≥ 1 under the hypotheses (r ≥ 1; nd = 0 forces r = 1)
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 37, Lemma 8.3

import Mathlib
import Definitions.Def_HasseHSG_Generator_HasseSpace
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QLogCurve
import Definitions.Def_HasseHSG_Generator_Wronskian

namespace HasseHSG.Generator

/-- Lemma 8.3 (p. 37): with `g₁, …, g_r` a basis of `∂̂* f` ending in `g_r = f`, `W ∈ F[q][t]` its
`D_{q,d}`-Wronskian and `q₀ ∈ F` with `q₀^m ≠ 1` for `1 ≤ m ≤ B − 1`: if `W(q₀, t) ≠ 0` then
`f ∘ p_{q₀} ≢ 0 mod t^B`. -/
theorem lemma_8_3 {F : Type*} [Field F] {n d r : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : MvPolynomial (Fin n) F) (hf : f.totalDegree ≤ d)
    (g : Module.Basis (Fin r) F (hasseSpace f)) (hr : 0 < r)
    (hgr : (g ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ : MvPolynomial (Fin n) F) = f)
    (w : Polynomial (Polynomial F))
    (hw : embFQTL w = wronskian a d (fun j => embFxL (g j : MvPolynomial (Fin n) F)))
    (q₀ : F) (hq₀ : ∀ m : ℕ, 1 ≤ m → (m : ℤ) ≤ Bnum n d r - 1 → q₀ ^ m ≠ 1)
    (hW : w.map (Polynomial.evalRingHom q₀) ≠ 0) :
    ¬ Polynomial.X ^ (Bnum n d r).toNat ∣
      MvPolynomial.aeval (truncCurve a q₀ (Bnum n d r).toNat) f := by sorry

end HasseHSG.Generator
