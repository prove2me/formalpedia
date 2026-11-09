-- Prove2me | Theorems.Thm_NadlerCLS_theorem_C_2_transfer
-- name    : NadlerCLS.theorem_C_2_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:15.607955+00:00
-- url     : https://prove2.me/theorems/a23124d3-ebbb-457d-a075-3bc141897b32
-- title:
--   Proof of Theorem C.2 — the transfer chain (C.5)
-- statement:
--   Let $f:[0,1]^n\to[0,1]^n$ and $p:[0,1]^n\to[0,1]$, $\lambda>0$, $0<\delta<1$, $\beta\in(0,1]$, $\bar\lambda=\max\{1,\lambda\}$, and $h=2^{-m}$ with $m\ge1$,
--   $$ nh\le1,\qquad 3\bar\lambda^2(nh)^{\beta^2}\le\delta/2 . \tag{C.4} $$
--   Let $\tilde f=I_hf$, $\tilde p=I_hp$, $x\in[0,1]^n$ and $z=\tilde f(x)$, and write $V(u)$ for the vertices selected at $u$. Assume
--
--   1. $\|f(x)-f(v)\|_1\le\lambda\|x-v\|_1^{\beta}$ for every $v\in V(x)$;
--   2. $|p(x)-p(v)|\le\lambda\|x-v\|_1^{\beta}$ for every $v\in V(x)$;
--   3. $|p(z)-p(v)|\le\lambda\|z-v\|_1^{\beta}$ for every $v\in V(z)$;
--   4. $|p(f(x))-p(z)|\le\lambda\|f(x)-z\|_1^{\beta}$;
--
--   and that $x$ is a target answer, $\tilde p(z)\ge\tilde p(x)-\delta/2$. Then
--   $$ p(f(x))\ge p(x)-\delta , $$
--   so $x$ is an (HO1) answer of the original instance.
--
--   This is the decoder's correctness when all four finite families of comparisons pass; a failed comparison is itself an (HO2) or (HO3) answer.
--
--   Differences from the source:
--   - generalization: $f$, $p$ well-behaved circuits and rational $\lambda,\delta$, fixed rational $\beta$ → arbitrary maps with the stated ranges on the cube, real $\lambda$, $\delta$ and $\beta$; reason: the chain is a real-analysis argument; circuits and rational parameters are a special case
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Theorem C.2, pp.34–36: (C.4), comparisons 1–4 (p.35), (C.5) and the chain after it (p.36)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_kuhnInterp

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Proof of Theorem C.2: the decoder's transfer chain (C.5)** (Xiong–Vlatakis-Gkaragkounis,
*On the Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held
version of 2026-11-03, sha256 1fcc5a02…6dc485, proof of Theorem C.2, pp.34–36, conditions (C.4),
comparisons 1–4 of p.35, and (C.5), p.36). Let `f : [0, 1]ⁿ → [0, 1]ⁿ`, `p : [0, 1]ⁿ → [0, 1]`,
`λ > 0`, `0 < δ < 1`, `β ∈ (0, 1]`, `λ̄ = max{1, λ}`, and `h = 2^{−m}` with `m ≥ 1`, `n h ≤ 1` and
`3 λ̄² (n h)^{β²} ≤ δ/2` (C.4). Let `f̃ = I_h f`, `p̃ = I_h p`, `x ∈ [0, 1]ⁿ` and `z = f̃(x)`. Assume

1. `‖f(x) − f(v)‖₁ ≤ λ ‖x − v‖₁^β` for every vertex `v` selected at `x`;
2. `|p(x) − p(v)| ≤ λ ‖x − v‖₁^β` for every vertex `v` selected at `x`;
3. `|p(z) − p(v)| ≤ λ ‖z − v‖₁^β` for every vertex `v` selected at `z`;
4. `|p(f(x)) − p(z)| ≤ λ ‖f(x) − z‖₁^β`;

and the target answer `p̃(z) ≥ p̃(x) − δ/2`. Then `p(f(x)) ≥ p(x) − δ`, i.e. `x` is an (HO1) answer.

**Formalization Note** `f`, `p` are arbitrary maps with the stated ranges on the cube; `p̃` is the
interpolant of `p` viewed as a map into `ℝ¹`; `β` and `λ` are real; `t^β` is `Real.rpow`. -/
theorem theorem_C_2_transfer (n : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (p : (Fin n → ℝ) → ℝ)
    (hf : ∀ x, InCube x → InCube (f x)) (hp : ∀ x, InCube x → 0 ≤ p x ∧ p x ≤ 1)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hnh : (n : ℝ) * kuhnH m ≤ 1)
    (hC4 : 3 * (max 1 lam) ^ 2 * ((n : ℝ) * kuhnH m) ^ (β ^ 2) ≤ δ / 2)
    (x : Fin n → ℝ) (hx : InCube x)
    (h1 : ∀ j, l1 (f x) (f (kuhnVertex m x j)) ≤ lam * (l1 x (kuhnVertex m x j)) ^ β)
    (h2 : ∀ j, |p x - p (kuhnVertex m x j)| ≤ lam * (l1 x (kuhnVertex m x j)) ^ β)
    (h3 : ∀ j, |p (kuhnInterp m f x) - p (kuhnVertex m (kuhnInterp m f x) j)| ≤
      lam * (l1 (kuhnInterp m f x) (kuhnVertex m (kuhnInterp m f x) j)) ^ β)
    (h4 : |p (f x) - p (kuhnInterp m f x)| ≤ lam * (l1 (f x) (kuhnInterp m f x)) ^ β)
    (htarget : kuhnInterp m (fun v (_ : Fin 1) => p v) (kuhnInterp m f x) 0 ≥
      kuhnInterp m (fun v (_ : Fin 1) => p v) x 0 - δ / 2) :
    p (f x) ≥ p x - δ := by sorry

end NadlerCLS
