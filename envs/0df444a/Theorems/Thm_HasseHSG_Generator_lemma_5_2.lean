-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_5_2
-- name    : HasseHSG.Generator.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:43.59821+00:00
-- url     : https://prove2.me/theorems/04c6745e-c7a1-41ab-b2f1-b0581ff56bac
-- title:
--   Lemma 5.2 — $D_{q,d}$ preserves $F(q)[t,x]$ and $F[q][t,x]$, does not raise $\deg_x$, raises $\deg_t$ by at most $nd-1$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   Let $f\in F(q)[t,x_1,\dots,x_n]$ with $\deg_x f\le d$, where $\deg_x$ is the total degree in $x$. Then $D_{q,d}(f)=Q_d(t)\tilde D_q(f)$ lies in $F(q)[t,x]$, and
--
--   $$\deg_x D_{q,d}(f)\le\deg_x f,\qquad \deg_t D_{q,d}(f)\le\deg_t f+nd-1.$$
--
--   Moreover, if $f\in F[q][t,x]$, then $D_{q,d}(f)\in F[q][t,x]$ and
--   $$\deg_q D_{q,d}(f)\le\deg_q f+\deg_t f+d-1.$$
--
--   These degree bounds drive the estimates $\deg_t W\le B-r$ and $\deg_q W\le R$ for the Wronskian (Lemma 8.1). Because $D_{q,d}$ maps polynomials of $x$-degree at most $d$ to polynomials of the same kind, it can be iterated.
--
--   **Formalization Note.** Membership in $F(q)[t,x]$ or $F[q][t,x]$ is an existential: a polynomial $g$ whose image in $B$ equals $D_{q,d}(f)$. Here $\deg_t$ is the largest $t$-degree of a coefficient and $\deg_q$ is the largest $q$-degree of a coefficient. The bounds are inequalities in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: deg 0 = −∞, so the t- and q-degree bounds hold trivially for D_{q,d}(f) = 0 → the bounds are asserted for D_{q,d}(f) ≠ 0, with natDegree in ℤ; reason: no instance changes: the zero polynomial satisfies the source's bounds by convention
--   - encoding: D_{q,d}(f) ∈ F(q)[t,x] (resp. F[q][t,x]) → there is g in MvPolynomial (Fin n) (F(q)[t]) (resp. (F[q])[t]) whose image in B is Q_d·D̃_q(f); reason: membership in a subring of B
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 21, Lemma 5.2

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-- Lemma 5.2 (p. 21). -/
theorem lemma_5_2 {F : Type*} [Field F] {n d : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (f : PolyQT F n) (hf : f.totalDegree ≤ d) :
    (∃ g : PolyQT F n, embedPoly g = DqdB a d (embedPoly f) ∧
      g.totalDegree ≤ f.totalDegree ∧
      (g ≠ 0 → (degT g : ℤ) ≤ (degT f : ℤ) + (n * d : ℕ) - 1)) ∧
    ∀ f' : PolyQTInt F n, embedInt f' = f →
      ∃ g' : PolyQTInt F n, embedPoly (embedInt g') = DqdB a d (embedPoly f) ∧
        (g' ≠ 0 → (degQ g' : ℤ) ≤ (degQ f' : ℤ) + (degT f' : ℤ) + (d : ℤ) - 1) := by sorry

end HasseHSG.Generator
