-- Prove2me | Theorems.Thm_MasulloGRH_exists_sequence_bounded_inv_partial_euler
-- name    : MasulloGRH.exists_sequence_bounded_inv_partial_euler
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:43:03.089187+00:00
-- url     : https://prove2.me/theorems/43cd773f-c20d-48e7-b651-b5d9249d5fe2
-- title:
--   Proposition B.5.3.2 — a sequence of ordinates on which the Euler factors at $S$ stay away from $0$
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $q_v=N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   Let $S_f$ be a finite set of finite places of $F$ such that $\chi$ is unramified at every $v\in S_f$. Then there are a real number $N_S>0$ and a sequence $(T_k)_{k\in\mathbb Z}$ of real numbers such that:
--
--   1. $T_k\ge 0$ for $k\ge0$, $T_k\le0$ for $k\le 0$, and $T_k\le T_{k+1}$ for every $k$;
--   2. $|T_k|\to+\infty$ as $|k|\to+\infty$;
--   3. for every $k\in\mathbb Z$,
--   $$\prod_{v\in S_f}\big|1-\chi(\mathfrak p_v)\,q_v^{-iT_k}\big|^{-1}\le N_S .$$
--
--   Each factor $1-\chi(\mathfrak p_v)q_v^{-it}$ vanishes for suitable real $t$; the proposition provides ordinates, tending to infinity in both directions, on which all the factors at $S_f$ are bounded away from $0$ at the same time.
--
--   **Formalization Note** Item 3 is stated as $1\le N_S\prod_{v\in S_f}|1-\chi(\mathfrak p_v)q_v^{-iT_k}|$, which is the same inequality and also says that no factor vanishes.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.5.3.2, Proposition B.5.3.2, eq. (B.5.3.3), p. 632

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem exists_sequence_bounded_inv_partial_euler
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : HeckeCharacter F) (hχ : ∀ v ∈ Sf, χ.IsUnramifiedAt v) :
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧
      (∀ k : ℤ, 0 ≤ k → 0 ≤ T k) ∧ (∀ k : ℤ, k ≤ 0 → T k ≤ 0) ∧ (∀ k : ℤ, T k ≤ T (k + 1)) ∧
      Filter.Tendsto (fun k : ℤ => |T k|) Filter.cofinite Filter.atTop ∧
      ∀ k : ℤ, 1 ≤ N * ∏ v ∈ Sf, ‖eulerFactorInv χ v (T k * Complex.I)‖ := by sorry

end MasulloGRH
