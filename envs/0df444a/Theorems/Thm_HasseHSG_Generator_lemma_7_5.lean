-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_7_5
-- name    : HasseHSG.Generator.lemma_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:46.751029+00:00
-- url     : https://prove2.me/theorems/5c1d716b-cd6b-4968-ae2c-c3ee6302d595
-- title:
--   Lemma 7.5 — the $D_{q,d}$-Wronskian of a basis of a $q$-partial closed space lies in $F(q)[t]$ and is nonzero
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3).
--
--   Let $V\subseteq F(q)[x_1,\dots,x_n]$ be a $q$-partial closed subspace consisting of polynomials of total degree at most $d$, and let $g_1,\dots,g_m$ be a basis of $V$. Then the Wronskian $W=W_{D_{q,d}}(g_1,\dots,g_m)$ is independent of $x$ and nonzero:
--
--   $$W\in F(q)[t]\qquad\text{and}\qquad W\neq0.$$
--
--   This $x$-freeness is what allows the substitution $x\mapsto p(t)$ to leave the Wronskian unchanged in the proof of Theorem 8.2.
--
--   **Formalization Note.** $W$ lives in $L$. "$W\in F(q)[t]$" means that $W$ is the image of some $w\in F(q)[t]$ under the inclusion `embFqTL`. The basis is a `Module.Basis (Fin m)` of $V$ over $F(q)$.
--
--   Differences from the source:
--   - encoding: W ∈ F(q)[t] → ∃ w : F(q)[t] whose image in L is W; reason: membership in a subring of L
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 34, Lemma 7.5 (proof pp. 34–35)

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_Wronskian
import Definitions.Def_HasseHSG_Generator_QPartial

namespace HasseHSG.Generator

/-- Lemma 7.5 (p. 34): the `D_{q,d}`-Wronskian of a basis of a `q`-partial closed subspace of
polynomials of degree at most `d` lies in `F(q)[t]` and is nonzero. -/
theorem lemma_7_5 {F : Type*} [Field F] {n d m : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (V : Submodule (Fq F) (MvPolynomial (Fin n) (Fq F))) (hV : IsQPartialClosed a V)
    (hdeg : ∀ g ∈ V, g.totalDegree ≤ d) (b : Module.Basis (Fin m) (Fq F) V) :
    (∃ w : Polynomial (Fq F), embFqTL w = wronskian a d (fun j => embFqxL (b j : _))) ∧
      wronskian a d (fun j => embFqxL (b j : _)) ≠ 0 := by sorry

end HasseHSG.Generator
