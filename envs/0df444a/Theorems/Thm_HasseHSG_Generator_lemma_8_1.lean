-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_8_1
-- name    : HasseHSG.Generator.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:34.356287+00:00
-- url     : https://prove2.me/theorems/7ea3e9e5-1e1d-4f68-bff9-a31ab0e52a21
-- title:
--   Lemma 8.1 — the Wronskian of a basis of $\hat\partial^*f$ is a nonzero element of $F[q][t]$ with $\deg_t W\le B-r$, $\deg_q W\le R$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   Let $f\in F[x_1,\dots,x_n]$ have total degree at most $d$, and let $g_1,\dots,g_r\in F[x]$ be a basis of the Hasse derivative space $\hat\partial^*f$. Then $W:=W_{D_{q,d}}(g_1,\dots,g_r)$ is a nonzero element of $F[q][t]$ with
--
--   $$\deg_t W\le B-r,\qquad \deg_q W\le R,$$
--
--   where $B=(nd-1)\binom r2+r$ and $R=(nd-1)\binom r3+(d-1)\binom r2$ are the integers of Eq. (19). Here $\deg_q W$ is the largest $q$-degree of a coefficient of $W$ as a polynomial in $t$.
--
--   The $t$-degree bound feeds Theorem 8.2. The $q$-degree bound says that $W(q_0,t)\neq0$ for some $q_0$ in any set of $R+1$ field elements, which the interpolation in the proof of Theorem 1.2 relies on.
--
--   **Formalization Note.** $W$ is computed in $L$ from the images of the $g_j$. "$W\in F[q][t]$ with the degree bounds" means: there is $w$ in `Polynomial (Polynomial F)` (outer variable $t$, inner variable $q$) whose image in $L$ is $W$, with $\deg w\le B-r$, and every coefficient of $w$ of $q$-degree at most $R$. These are inequalities in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: W ∈ F[q][t] with deg_t W ≤ B − r and deg_q W ≤ R → ∃ w : (F[q])[t] with image W in L, natDegree w ≤ B − r and natDegree (coeff k w) ≤ R for all k (in ℤ); reason: membership in a subring of L; the q-degree of a polynomial in t is the maximum over its coefficients
--   - encoding: B, R of Eq. (19) → Bnum, Rnum in ℤ; reason: nd − 1 can be −1
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
--   - generalization: the opening of §8 fixes a nonzero f before Lemma 8.1 restates the degree and basis hypotheses → f may also be zero; reason: the original nonzero instances are retained; for f = 0 the Hasse space has dimension r = 0, the empty Wronskian is 1, and B = R = 0, so both degree bounds are 0 ≤ 0
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 35, Lemma 8.1 (proof pp. 35–36)

import Mathlib
import Definitions.Def_HasseHSG_Generator_HasseSpace
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_QLogCurve
import Definitions.Def_HasseHSG_Generator_Wronskian

namespace HasseHSG.Generator

/-- Lemma 8.1 (p. 35): for `f ∈ F[x]` of degree at most `d` and a basis `g₁, …, g_r` of `∂̂* f`,
`W = W_{D_{q,d}}(g₁, …, g_r)` is a nonzero element of `F[q][t]` with `deg_t W ≤ B − r` and
`deg_q W ≤ R`. -/
theorem lemma_8_1 {F : Type*} [Field F] {n d r : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : MvPolynomial (Fin n) F) (hf : f.totalDegree ≤ d) (g : Module.Basis (Fin r) F (hasseSpace f)) :
    wronskian a d (fun j => embFxL (g j : MvPolynomial (Fin n) F)) ≠ 0 ∧
    ∃ w : Polynomial (Polynomial F),
      embFQTL w = wronskian a d (fun j => embFxL (g j : MvPolynomial (Fin n) F)) ∧
      (w.natDegree : ℤ) ≤ Bnum n d r - r ∧
      ∀ k, ((w.coeff k).natDegree : ℤ) ≤ Rnum n d r := by sorry

end HasseHSG.Generator
