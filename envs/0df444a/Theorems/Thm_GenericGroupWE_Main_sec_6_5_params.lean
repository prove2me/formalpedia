-- Prove2me | Theorems.Thm_GenericGroupWE_Main_sec_6_5_params
-- name    : GenericGroupWE.Main.sec_6_5_params
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:14.879047+00:00
-- url     : https://prove2.me/theorems/e110aac7-3cb5-419d-9ae4-4cc0cc1fb8c3
-- title:
--   §6.5, eq. (33) and choice of d — Matrix order and the polylogarithmic gap
-- statement:
--   For every fixed integer $d\ge1$, let $r,R,m$ be the exact functions of $N$ in (26) and (33). There is a positive constant $C$ depending only on $d$ such that $N\le m\le CN^C$ for $N\ge2$. Moreover, for every $c>0$ with $d>2c$, some threshold depending on $c,d$ satisfies
--
--   $$R\ge(\log_2m)^c\quad\text{for every }N\text{ beyond that threshold}.$$
--
--   The item also retains the displayed two-sided estimates $R=\Theta_d(r^d)=\Theta_d((\log_2N)^{d/2})=\Theta_d((\log_2m)^{d/2})$, the logarithmic binomial estimate, its $O_d(\sqrt{\log N}\log\log N)$ bound, and the $o(\log N)$ assertion. Every asymptotic has explicit constants and thresholds before $N$.
--
--   Differences from the source:
--   - encoding: r=max(1,floor(sqrt(log_2(N+2)))) → r=max(1,Nat.sqrt(Nat.log 2 (N+2))); reason: integer square root of the logarithm floor equals the source floor of the real square root
--   - encoding: O, Theta and little-o notation → positive constants, two-sided eventual bounds and quantified epsilon bounds; reason: all uniformities and all sufficiently-large thresholds are explicit
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §6.5, eq. (33) and choice of d, PDF p. 30 (printed p. 29).

import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main
open scoped BigOperators

theorem sec_6_5_params :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, 2 ≤ N → N ≤ matrixOrder N d ∧
        (matrixOrder N d : ℝ) ≤ C * (N : ℝ)^C) ∧
      (∀ c : ℝ, 0 < c → 2*c < (d : ℝ) →
        ∃ threshold : ℕ, 2 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
          (Real.logb 2 (matrixOrder N d : ℝ))^c ≤ (rankTarget N d : ℝ)) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          a * (weightDegree N : ℝ)^d ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (weightDegree N : ℝ)^d ∧
          a * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ∧
          a * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
            ε * Real.logb 2 (N : ℝ)) ∧
      (∀ N : ℕ, 2 ≤ N →
        Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
          (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ)) ∧
      (∃ threshold : ℕ, 4 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
        (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
          C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ))) := by sorry

end GenericGroupWE.Main
