-- Prove2me | Theorems.Thm_MultiNashRepair_theorem_5_8
-- name    : MultiNashRepair.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:49.862196+00:00
-- url     : https://prove2.me/theorems/1baebd56-9236-4ac4-84dc-066e7580cf6f
-- title:
--   Theorem 5.8 — optimality of the scalar certificate: $\sigma_\star=\max_f\min_H K_f(H)=\max_s H_c(s)$, uniquely at $f_\star$
-- statement:
--   Let $s_\star$ be the unique zero of $Q_c(s)=2s^3-2s^2-2s+1$ on $[0,1/2]$, $f_\star=1-s_\star$, and $\sigma_\star$ the unique root in $(1,2)$ of $\sigma^3-19\sigma^2+27\sigma+1$. Then:
--   1. $7/12<f_\star<3/5$, $2/5<s_\star<5/12$ and $2f_\star^3-4f_\star^2+1=0$;
--   2. $\sigma_\star=H_c(s_\star)=9-16f_\star+6f_\star^2$;
--   3. $119/75<\sigma_\star<2$, $\sigma_\star$ is a root of the cubic, and it is the only root in $(1,2)$;
--   4. for every $H\ge0$, $$K_{f_\star}(H)-\sigma_\star=\frac{(2f_\star-1)(H-s_\star)^2}{f_\star(f_\star+H)}\qquad(5.39);$$
--   5. for every $f>0$, $$\sigma_\star-K_f(s_\star)=\frac{\sigma_\star(f-f_\star)^2}{f(f+s_\star)}\qquad(5.40);$$
--   6. $$\sigma_\star=\max_{0<f<1}\ \min_{0\le H\le f}K_f(H)=\max_{0\le s\le1/2}H_c(s)\qquad(5.41),$$ and $f_\star$ is the unique maximizing activation fraction.
--
--   This identifies the approximation constant of Theorem 1.1 as the value of the scalar max–min problem that the potential argument certifies.
--
--   Differences from the source:
--   - generalization: Theorem 5.8's three displays → also the p.35 characterization: bounds on $s_\star,f_\star$, $2f_\star^3-4f_\star^2+1=0$, $\sigma_\star=H_c(s_\star)=9-16f_\star+6f_\star^2$, $119/75<\sigma_\star<2$, root uniqueness; reason: these are stated on the same page (before the theorem and in its proof) and link the paper's $\sigma_\star:=H_c(s_\star)$ to the root of Theorem 1.1; the item contains Theorem 5.8
--   - encoding: $s_\star$, $\sigma_\star$ as roots → suprema `sStar`, `sigmaStar`; reason: monotonicity makes the suprema the roots
--   - encoding: $\max_{0<f<1}\min_{0\le H\le f}K_f(H)$ and $\max_s H_c(s)$ → `IsGreatest` of the images of $U$ on $(0,1)$ and of $H_c$ on $[0,1/2]$, with $U$ an infimum; reason: attainment of the inner minimum is Lemma 5.9
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Theorem 5.8, (5.39)–(5.41), p.35, with the characterization of s⋆, f⋆, σ⋆ before it and the root argument of its proof (p.35)

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate

namespace MultiNashRepair

/-- **Theorem 5.8 (Optimality of the Scalar Certificate)**, with the characterization of `s⋆`,
`f⋆`, `σ⋆` that precedes it and the root argument of its proof (Tang, Ding, Fang,
arXiv:2611.06076, p.35).

1. `7/12 < f⋆ < 3/5` (equivalently `2/5 < s⋆ < 5/12`) and `2f⋆³ − 4f⋆² + 1 = 0`.
2. `σ⋆ = H_c(s⋆) = 9 − 16 f⋆ + 6 f⋆²`, linking the paper's p.35 definition of `σ⋆` to the root
   of Theorem 1.1.
3. `119/75 < σ⋆ < 2`, `σ⋆³ − 19σ⋆² + 27σ⋆ + 1 = 0`, and `σ⋆` is the only root in `(1, 2)`.
4. (5.39) `K_{f⋆}(H) − σ⋆ = (2f⋆ − 1)(H − s⋆)² / (f⋆(f⋆ + H))` for every `H ≥ 0`.
5. (5.40) `σ⋆ − K_f(s⋆) = σ⋆ (f − f⋆)² / (f (f + s⋆))` for every `f > 0`.
6. (5.41) `σ⋆ = max_{0<f<1} min_{0≤H≤f} K_f(H) = max_{0≤s≤1/2} H_c(s)`, and `f⋆` is the unique
   maximizing activation parameter.

**Formalization Note.** `s⋆`, `f⋆`, `σ⋆` are the suprema `sStar`, `fStar = 1 − sStar`,
`sigmaStar` of the definition module; `U f` is `min_{0≤H≤f} K_f(H)`. -/
theorem theorem_5_8 :
    (7 / 12 < fStar ∧ fStar < 3 / 5 ∧ 2 / 5 < sStar ∧ sStar < 5 / 12 ∧
      2 * fStar ^ 3 - 4 * fStar ^ 2 + 1 = 0) ∧
    (Hc sStar = sigmaStar ∧ sigmaStar = 9 - 16 * fStar + 6 * fStar ^ 2) ∧
    (119 / 75 < sigmaStar ∧ sigmaStar < 2 ∧ sigmaPoly sigmaStar = 0 ∧
      ∀ s ∈ Set.Ioo (1 : ℝ) 2, sigmaPoly s = 0 → s = sigmaStar) ∧
    (∀ H : ℝ, 0 ≤ H →
      Kf fStar H - sigmaStar = (2 * fStar - 1) * (H - sStar) ^ 2 / (fStar * (fStar + H))) ∧
    (∀ f : ℝ, 0 < f →
      sigmaStar - Kf f sStar = sigmaStar * (f - fStar) ^ 2 / (f * (f + sStar))) ∧
    (IsGreatest (U '' Set.Ioo 0 1) sigmaStar ∧
      (∀ f ∈ Set.Ioo (0 : ℝ) 1, U f = sigmaStar → f = fStar) ∧
      IsGreatest (Hc '' Set.Icc 0 (1 / 2)) sigmaStar) := by sorry

end MultiNashRepair
