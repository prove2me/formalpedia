-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_4_8
-- name    : HoneycombCodes.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:33.584451+00:00
-- url     : https://prove2.me/theorems/211b43aa-8fa9-4afa-a5ac-62427dea371f
-- title:
--   Theorem 4.8 — finite honeycomb bound for $A_2(n,d)$
-- statement:
--   Fix $n$, $0\le k\le n/2$, and a finite set $\Omega$ of valid triples $(i,j,\ell)$ that is connected in the positive-weight box-transfer graph; let $p_{\omega,\omega'}$ be the exact two-row transfer weights, $D_\omega$ the ambient dimensions (37), $d_k=f_{(n-k,k)}$ (36) and $J_\Omega=(\sqrt{p_{\omega,\omega'}p_{\omega',\omega}})$. Let $1\le d\le n/2$ and $s=1-2d/n$.
--
--   1. For every positive profile $w$ with $\lambda_\Omega(w)=\min_\nu\sum_\omega p_{\omega,\nu}w_\omega/w_\nu>s$,
--   $$
--   A_2(n,d)\le\frac{1-s}{d_k(\lambda_\Omega(w)-s)}\,D_\Omega(w),\qquad D_\Omega(w)=\frac{(\sum_\omega w_\omega)^2}{\sum_\omega w_\omega^2/D_\omega}. \tag{38}
--   $$
--   2. If $v$ is the positive unit Perron vector of $J_\Omega$ and $\Lambda_\Omega=\lambda_{max}(J_\Omega)>s$, then
--   $$
--   A_2(n,d)\le\frac{1-s}{d_k(\Lambda_\Omega-s)}\Bigl(\sum_{\omega\in\Omega}\sqrt{D_\omega}\,v_\omega\Bigr)^2\le\frac{1-s}{d_k(\Lambda_\Omega-s)}\sum_{\omega\in\Omega}D_\omega. \tag{39–40}
--   $$
--
--   Here $A_2(n,d)$ is the largest size of a binary code of length $n$ and minimum distance at least $d$. This is the finite-length coding theorem whose asymptotics give the honeycomb exponent.
--
--   Differences from the source:
--
--   - reading: contraction coefficients p_{ω,ω′} 'using Theorem 4.4' (squared 6j symbols, Racah factor R²_{στ}) → the closed forms (32)–(33) with R²_{σσ} = Q_σ, R²_{σ,1−σ} = 1 − Q_σ from Remark 4.7 and (117), set to 0 when an endpoint is not valid; reason: Remark 4.7 and App. A.2 identify the squared Racah factors with this closed form, which is what the paper computes with
--   - encoding: the positive unit Perron vector v of J_Ω → any v with positive entries, Σ v_ω² = 1 and J_Ω v = λ_max(J_Ω) v, with λ_max the published BlockBochner.lamMax; reason: for a connected nonnegative symmetric matrix this vector is unique, so the two quantifications agree
--   - encoding: binary codes in {±1}ⁿ and A₂(n, d) → the published PrettyGoodCriterion.A2 (codes as Finsets of words Fin n → Fin 2); reason: {±1} and Fin 2 are in bijection and Hamming distance is preserved
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §4.4, Theorem 4.8, eqs. (38)–(40), p.24 (PDF 26); setup pp.23–24

import Mathlib
import Definitions.Def_HoneycombCodes_pDir
import Definitions.Def_HoneycombCodes_lamProfile
import Definitions.Def_BlockBochner_lamMax
import Definitions.Def_PrettyGoodCriterion_rateFunction

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 4.8 (finite honeycomb bound)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.24 (PDF 26). Fix `n`, `k` with
`0 ≤ k ≤ n/2`, and a finite set `Ω` of valid triples that is connected in the positive-weight
box-transfer graph. Let `1 ≤ d ≤ n/2` and `s = 1 − 2d/n`. For every positive profile `w` with
`λ_Ω(w) > s`, `A₂(n, d) ≤ (1 − s)/(d_k(λ_Ω(w) − s)) D_Ω(w)` (38). If `v` is the positive unit
Perron vector of `J_Ω` and `Λ_Ω = λ_max(J_Ω) > s`, then
`A₂(n, d) ≤ (1 − s)/(d_k(Λ_Ω − s)) (Σ √D_ω v_ω)²` (39) `≤ (1 − s)/(d_k(Λ_Ω − s)) Σ D_ω` (40).

**Formalization Note.** The weights `p_{ω,ω′}` are the closed forms (32)–(33) with the Racah
factor of Remark 4.7 (`pDir`), `D_ω` is (37), `d_k` is (36), `J_Ω` is `JOmega`. `λ_Ω(w)`,
`D_Ω(w)` are `lamProfile`, `effDim` of the weights restricted to `Ω`. `A₂` is the published
`PrettyGoodCriterion.A2` (codes in `Fin n → Fin 2`). The Perron vector is any positive unit
eigenvector of `J_Ω` for `λ_max(J_Ω)` (`BlockBochner.lamMax` (the published largest-eigenvalue definition)). -/
theorem theorem_4_8 (n k d : ℕ) (hk : 2 * k ≤ n) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ n)
    (Ω : Finset (ℕ × ℕ × ℕ)) (hvalid : ∀ ω ∈ Ω, IsValidTriple n k ω)
    (hconn : IsConnectedOmega n k Ω) :
    let s : ℝ := 1 - 2 * (d : ℝ) / n
    (∀ w : Ω → ℝ, (∀ ω, 0 < w ω) →
      s < lamProfile (fun a b : Ω => pDir n k a b) w →
      (PrettyGoodCriterion.A2 n d : ℝ) ≤
        (1 - s) / (dk n k * (lamProfile (fun a b : Ω => pDir n k a b) w - s)) *
          effDim (fun ω : Ω => Domega n ω) w) ∧
    (∀ v : Ω → ℝ, (∀ ω, 0 < v ω) → ∑ ω, v ω ^ 2 = 1 →
      (JOmega n k Ω).mulVec v = BlockBochner.lamMax (JOmega n k Ω) • v →
      s < BlockBochner.lamMax (JOmega n k Ω) →
      (PrettyGoodCriterion.A2 n d : ℝ) ≤
          (1 - s) / (dk n k * (BlockBochner.lamMax (JOmega n k Ω) - s)) *
            (∑ ω : Ω, Real.sqrt (Domega n ω) * v ω) ^ 2 ∧
        (1 - s) / (dk n k * (BlockBochner.lamMax (JOmega n k Ω) - s)) *
            (∑ ω : Ω, Real.sqrt (Domega n ω) * v ω) ^ 2 ≤
          (1 - s) / (dk n k * (BlockBochner.lamMax (JOmega n k Ω) - s)) * ∑ ω : Ω, Domega n ω) := by sorry

end HoneycombCodes
