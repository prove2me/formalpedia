-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_B_2
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:09:36.364893+00:00
-- url     : https://prove2.me/theorems/e32e0077-8f4b-479c-9985-92528124f8ed
-- title:
--   Theorem B.2 — impact capacity
-- statement:
--   Fix $1\le b<n$, $y\in H_L(G)$, exact audits, a scale $\tau>0$ and $q\le n$. The alternatives are the fields $x\in H_L(G)$ with $|\operatorname{supp}(x-y)|\le b$ and $|\mu(x)-\mu(y)|\ge\tau$, and $\beta^{\mathrm{imp}}_q(y,\tau)$ is the optimal worst-case miss probability with no false positives, allowing randomization and adaptivity.
--
--   1. For a proper $S\subsetneq V$, the largest change of the mean among Lipschitz completions of $y$ outside $S$ is $a_y(S)$, attained by $U^S$ or $\Lambda^S$.
--   2. If $A_{b,\tau}(y)\ne\emptyset$, then
--   $$\beta^{\mathrm{imp}}_q(y,\tau)=\min_{\pi\in\Delta(\{Q:|Q|\le q\})}\ \max_{S\in A_{b,\tau}(y)}\Pr_{Q\sim\pi}(Q\cap S=\emptyset),$$
--   and adaptivity does not improve this value.
--   3. For $y=c\mathbf 1$, with $D_G(S)=\sum_{v\in S}d_G(v,V\setminus S)$, $a_y(S)=LD_G(S)/n$ and $A_{b,\tau}(c\mathbf 1)=\{S:1\le|S|\le b,\ D_G(S)\ge n\tau/L\}$.
--
--   Differences from the source:
--   - encoding: randomized adaptive detectors → probability mass functions over deterministic adaptive strategies; reason: private randomness drawn before the run; finite distributions are included
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem B.2, printed p.25 (PDF p.27)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Detection

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem B.2, printed p.25 / PDF p.27. `1 ≤ b < n`, `y ∈ H_L(G)`, `τ > 0`, `q ≤ n`.
1. For a proper `S ⊊ V`, the largest change of the mean among `L`-Lipschitz completions of `y`
   outside `S` is `a_y(S)`, attained by `U^S` or `Λ^S` (both are such completions).
2. If `A_{b,τ}(y) ≠ ∅`, `β^imp_q(y, τ) = min_π max_{S ∈ A_{b,τ}(y)} Pr_{Q∼π}(Q ∩ S = ∅)` over
   distributions on sets of at most `q` audits (attained), and adaptivity does not improve it.
3. For `y = c1`, `a_y(S) = L D_G(S)/n` and `A_{b,τ}(c1) = {S : 1 ≤ |S| ≤ b, D_G(S) ≥ nτ/L}`. -/
theorem theorem_B_2 {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (b q : ℕ) (τ : ℝ)
    (y : Fin n → ℝ) (hG : G.Connected) (hL : 0 < L) (hb1 : 1 ≤ b) (hbn : b < n) (hτ : 0 < τ)
    (hy : LipOn G L y) (hq : q ≤ n) :
    (∀ S : Finset (Fin n), S ≠ Finset.univ →
      LipOn G L (capUp G L y S) ∧ (∀ v ∉ S, capUp G L y S v = y v) ∧
      LipOn G L (capLow G L y S) ∧ (∀ v ∉ S, capLow G L y S v = y v) ∧
      IsGreatest {d : ℝ | ∃ x, LipOn G L x ∧ (∀ v ∉ S, x v = y v) ∧ d = |umean x - umean y|}
        (impactCap G L y S) ∧
      (|umean (capUp G L y S) - umean y| = impactCap G L y S ∨
        |umean (capLow G L y S) - umean y| = impactCap G L y S)) ∧
    ((capFamily G L b τ y).Nonempty →
      ∃ π₀ : PMF (Finset (Fin n)), AuditDist q π₀ ∧
        optMiss q y (impactAlt G L b τ y) = ⨆ S ∈ capFamily G L b τ y, avoidProb π₀ S ∧
        ∀ π : PMF (Finset (Fin n)), AuditDist q π →
          (⨆ S ∈ capFamily G L b τ y, avoidProb π₀ S) ≤ ⨆ S ∈ capFamily G L b τ y, avoidProb π S) ∧
    (∀ c : ℝ,
      (∀ S : Finset (Fin n), S ≠ Finset.univ →
        impactCap G L (fun _ => c) S = L * depthReal G S / n) ∧
      capFamily G L b τ (fun _ => c) =
        {S | 1 ≤ S.card ∧ S.card ≤ b ∧ n * τ / L ≤ depthReal G S}) := by sorry

end MeanCertificates1424.Hardness.Supplement
