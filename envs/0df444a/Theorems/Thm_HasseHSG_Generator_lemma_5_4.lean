-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_5_4
-- name    : HasseHSG.Generator.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:29.323233+00:00
-- url     : https://prove2.me/theorems/afcc8071-fd40-4500-849a-a9ec9a50bcc1
-- title:
--   Lemma 5.4 (q-chain rule) — $Q_d(t)\,\frac{d_q}{dt}(f\circ p)=D_{q,d}(f)\circ p$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $p=(p_1,\dots,p_n)$ be the $q$-logarithmic curve $p_i(t)=\sum_{m\ge1}(a_it)^m/[m]_q\in F(q)[[t]]$ (Eq. (15)), and $Q_d(t)=\prod_i(1-a_it)^d$.
--
--   For every $f\in F(q)[t,x]$ with $\deg_x f\le d$,
--
--   $$Q_d(t)\cdot\frac{d_q}{dt}(f\circ p)=D_{q,d}(f)\circ p\qquad\text{in }F(q)[[t]].$$
--
--   Here $\frac{d_q}{dt}h=(h(qt)-h(t))/((q-1)t)$. The substitution $x\mapsto p(t)$ intertwines $D_{q,d}$ with the $q$-derivative in $t$. This is what transfers vanishing order along $p$ from $f$ to its iterates $D_{q,d}^i f$ (Corollary 5.5).
--
--   **Formalization Note.** $D_{q,d}(f)$ is the polynomial `DqdPoly a d f` (Lemma 5.2 shows that it exists). $f\circ p$ is `MvPolynomial.eval₂` with the coefficients in $F(q)[t]$ mapped into $F(q)[[t]]$.
--
--   Differences from the source:
--   - encoding: D_{q,d}(f), a polynomial by Lemma 5.2 → DqdPoly a d f, the polynomial whose image in B is Q_d·D̃_q(f) (placeholder 0 only off the domain deg_x f ≤ d); reason: the item is stated only on the domain deg_x f ≤ d, where the two agree
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 23, Lemma 5.4

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QLogCurve

namespace HasseHSG.Generator

/-- Lemma 5.4 (q-chain rule, p. 23). -/
theorem lemma_5_4 {F : Type*} [Field F] {n d : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : PolyQT F n) (hf : f.totalDegree ≤ d) :
    (QdPoly a d : PowerSeries (Fq F)) * qDerivT (compP a f) = compP a (DqdPoly a d f) := by sorry

end HasseHSG.Generator
