-- Prove2me | Theorems.Thm_NadlerCLS_lemma_C_1
-- name    : NadlerCLS.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:46.420849+00:00
-- url     : https://prove2.me/theorems/c15e3acf-9e2c-4627-a697-77536a20bd4c
-- title:
--   Lemma C.1 (i)–(iii) — properties of the simplex-based interpolant (computational part: lemma_C_1_circuit)
-- statement:
--   Let $g:[0,1]^n\to[0,1]^r$, let $m\ge1$, $h=2^{-m}$, and let $I_hg$ be the simplex-based interpolant with vertices $v_0,\dots,v_n$ and weights $w_0,\dots,w_n$ selected at $x$.
--
--   1. **(i)** For every $x\in[0,1]^n$: $w_j\ge0$ and $\sum_jw_j=1$; every $v_j$ is a grid point of the cube (each coordinate equals $c\,h$ with $c\in\{0,\dots,2^m\}$) with $\|x-v_j\|_1\le nh$; $x=\sum_jw_jv_j$; and $I_hg(x)\in[0,1]^r$. Thus $I_hg(x)$ is a convex combination of the values of $g$ at $n+1$ grid vertices within $\ell_1$-distance $nh$ of $x$.
--   2. **(ii)** For all $x,y\in[0,1]^n$,
--   $$ \|I_hg(x)-I_hg(y)\|_1\le\frac rh\,\|x-y\|_1 . $$
--   3. **(iii)** For all reals $\lambda$ and $\beta\in(0,1]$ and every $x\in[0,1]^n$: if every vertex $v$ used at $x$ satisfies $\|g(x)-g(v)\|_1\le\lambda\|x-v\|_1^{\beta}$, then
--   $$ \|g(x)-I_hg(x)\|_1\le\lambda\,(nh)^{\beta}. $$
--
--   The Lipschitz bound (ii) holds whatever the regularity of $g$; this is what removes the Hölder violations in Theorem C.2.
--
--   Differences from the source:
--   - generalization: $g$ represented by a well-behaved circuit → any map $g$ of the cube into $[0,1]^r$; reason: (i)–(iii) are properties of the interpolation formula; the proof notes that it does not require $g$ to be continuous; circuits are a special case
--   - generalization: the fixed rational $\beta\in(0,1]$ and the instance's $\lambda$ → any real $\beta\in(0,1]$ and any real $\lambda$; reason: the bound is a real-analysis statement; the paper's parameters are a special case
--   - encoding: $n+1$ grid vertices and a permutation $\pi$ → vertices and weights indexed by `Fin (n + 1)` from $0$, the permutation given by the 0-based rank formula of p.34; reason: the rank formula is the paper's own construction of $\pi$; same vertices and weights
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Lemma C.1 (i)–(iii), pp.31–32, proved on pp.32–33

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_kuhnInterp

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Lemma C.1 (i)–(iii): properties of the simplex-based interpolant** (Xiong–Vlatakis-Gkaragkounis,
*On the Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held
version of 2026-11-03, sha256 1fcc5a02…6dc485, Lemma C.1, pp.31–32, proved on pp.32–33). Let
`g : [0, 1]ⁿ → [0, 1]ʳ`, `m ≥ 1` and `h = 2^{−m}`, and let `I_h g = kuhnInterp m g`.

(i) At every `x ∈ [0, 1]ⁿ` the `n + 1` weights are nonnegative and sum to one, every selected vertex
is a grid point of the cube (each coordinate is `c h` with `c ∈ {0, …, 2^m}`) at ℓ₁-distance at most
`n h` from `x`, `x = ∑ w_j v_j`, and `I_h g(x) ∈ [0, 1]ʳ`.

(ii) For all `x, y ∈ [0, 1]ⁿ`, `‖I_h g(x) − I_h g(y)‖₁ ≤ (r/h) ‖x − y‖₁`.

(iii) For all real `λ` and `β ∈ (0, 1]` and every `x ∈ [0, 1]ⁿ`: if every vertex `v` used at `x`
satisfies `‖g(x) − g(v)‖₁ ≤ λ ‖x − v‖₁^β`, then `‖g(x) − I_h g(x)‖₁ ≤ λ (n h)^β`.

**Formalization Note** `g` is an arbitrary map of the cube into the cube (the paper's circuit
representation matters only for the construction, `lemma_C_1_circuit`); `λ` and `β` are real. -/
theorem lemma_C_1 (n r m : ℕ) (hm : 1 ≤ m) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (hg : ∀ v, InCube v → InCube (g v)) :
    (∀ x : Fin n → ℝ, InCube x →
      (∀ j, 0 ≤ kuhnWeight m x j) ∧ ∑ j, kuhnWeight m x j = 1 ∧
      (∀ j i, ∃ c : ℕ, c ≤ 2 ^ m ∧ kuhnVertex m x j i = (c : ℝ) * kuhnH m) ∧
      (∀ j, l1 x (kuhnVertex m x j) ≤ (n : ℝ) * kuhnH m) ∧
      x = ∑ j, kuhnWeight m x j • kuhnVertex m x j ∧
      InCube (kuhnInterp m g x)) ∧
    (∀ x y : Fin n → ℝ, InCube x → InCube y →
      l1 (kuhnInterp m g x) (kuhnInterp m g y) ≤ (r : ℝ) / kuhnH m * l1 x y) ∧
    (∀ lam β : ℝ, 0 < β → β ≤ 1 → ∀ x : Fin n → ℝ, InCube x →
      (∀ j, l1 (g x) (g (kuhnVertex m x j)) ≤ lam * (l1 x (kuhnVertex m x j)) ^ β) →
      l1 (g x) (kuhnInterp m g x) ≤ lam * ((n : ℝ) * kuhnH m) ^ β) := by sorry

end NadlerCLS
