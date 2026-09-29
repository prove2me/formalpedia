-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE
-- name    : LanglandsTunnell.RankinSelberg.clearedFE_of_sum_mul_of_termwise_clearedFE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/9b28e542-df19-5438-af46-4aaba2919c1e
-- title:
--   Cleared functional equation for a sum of products
-- statement:
--   Fix a natural number $N$ with $1 < N$ and finite index types $\iota,\kappa$. Given complex constants $c, c_D, \Gamma_A, \Gamma_Z, \Gamma$ and integers $k_D, k_A, k_Z, k$ with $\Gamma = c_D\Gamma_A\Gamma_Z$ and $k = k_D + k_A + k_Z$; functions $\Psi,\Psi_d : \mathbb{C}\to\mathbb{C}$ and families $A, A_d, Z, Z_d : \iota \to \kappa \to \mathbb{C}\to\mathbb{C}$; polynomials $P, P_d, Q, Q_d \in \mathbb{C}[X]$ with $Q \neq 0$ and $Q_d \neq 0$; integers $m, m_d$ and reals $\sigma_2,\sigma_3$. Assume: on $\operatorname{Re} s > \sigma_2$ one has $\Psi(s)\,Q(N^{-s}) = N^{ms}P(N^{-s})$, and on $\operatorname{Re} s > \sigma_3$ one has $\Psi_d(s)\,Q_d(N^{-s}) = N^{m_d s}P_d(N^{-s})$; on some right half-plane $\Psi(s) = c\sum_{i}\sum_{j} A_{ij}(s)Z_{ij}(s)$, and on some right half-plane $\Psi_d(s) = c\,c_D N^{k_D s}\sum_i\sum_j (A_d)_{ij}(s)(Z_d)_{ij}(s)$; and for each pair $(i,j)$ there exist polynomials $P_A, P_{Ad}, Q_A, Q_{Ad}$ with $Q_A, Q_{Ad} \neq 0$, integers $m_A, m_{Ad}$ and reals $\sigma_A,\sigma_{Ad}$ such that $A_{ij}$ and $(A_d)_{ij}$ admit these rational forms in $N^{-s}$ on the corresponding half-planes and the identity $N^{m_{Ad}s}P_{Ad}(N^{-s})\,Q_A(N^{s}) = \Gamma_A N^{k_A s}\,N^{-m_A s}P_A(N^{s})\,Q_{Ad}(N^{-s})$ holds for all $s \in \mathbb{C}$, and similarly for $Z_{ij}, (Z_d)_{ij}$ with data $\Gamma_Z, k_Z$. The conclusion is that for every $s \in \mathbb{C}$, $N^{m_d s}P_d(N^{-s})\,Q(N^{s}) = \Gamma N^{ks}\,N^{-ms}P(N^{s})\,Q_d(N^{-s})$. (In the Lean the left-hand sides carry the factor $1$ evaluated at $N^{s}$, and $\Gamma$, $\Gamma_A$, $\Gamma_Z$ occur as constant polynomials evaluated at $N^{s}$.)
--
--   This is the multiplicativity step for cleared functional equations of rational functions of $X = N^{-s}$: termwise functional equations for the factors $A_{ij}, Z_{ij}$ of a finite sum of products propagate, with gamma factor $c_D\Gamma_A\Gamma_Z$ and shift $k_D+k_A+k_Z$, to the cleared functional equation of the sum. It is pure algebra of rational functions and is used in assembling the functional equation of the local Rankin–Selberg integrals from the functional equations of their Whittaker and torus-zeta constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.clearedFE_of_sum_mul_of_termwise_clearedFE
    (N : ℕ) (hN : 1 < N)
    (ι κ : Type) [Fintype ι] [Fintype κ]
    (c cD ΓA ΓZ Γ : ℂ) (kD kA kZ k : ℤ) (hΓ : Γ = cD * ΓA * ΓZ) (hk : k = kD + kA + kZ)
    (Ψ Ψd : ℂ → ℂ) (A Ad Z Zd : ι → κ → ℂ → ℂ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hrat : (∀ s : ℂ, σ₂ < s.re → Ψ s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (hratd : (∀ s : ℂ, σ₃ < s.re → Ψd s * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))))
    (hsum : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Ψ s = c * ∑ i, ∑ j, A i j s * Z i j s)
    (hsumd : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Ψd s = c * (cD * (N : ℂ) ^ ((kD : ℂ) * s) * ∑ i, ∑ j, Ad i j s * Zd i j s))
    (hA : ∀ (i : ι) (j : κ), ∃ (PA PAd QA QAd : Polynomial ℂ) (mA mAd : ℤ) (σA σAd : ℝ), QA ≠ 0 ∧ QAd ≠ 0 ∧
      (∀ s : ℂ, σA < s.re → A i j s * QA.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σAd < s.re → Ad i j s * QAd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) *
            QA.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓA).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kA : ℂ) * s)) *
            ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) *
            QAd.eval ((N : ℂ) ^ (-s))))
    (hZ : ∀ (i : ι) (j : κ), ∃ (PZ PZd QZ QZd : Polynomial ℂ) (mZ mZd : ℤ) (σZ σZd : ℝ), QZ ≠ 0 ∧ QZd ≠ 0 ∧
      (∀ s : ℂ, σZ < s.re → Z i j s * QZ.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZ : ℂ) * s) * PZ.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σZd < s.re → Zd i j s * QZd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) *
            QZ.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓZ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kZ : ℂ) * s)) *
            ((N : ℂ) ^ ((mZ : ℂ) * (-s)) * PZ.eval ((N : ℂ) ^ s)) *
            QZd.eval ((N : ℂ) ^ (-s)))) :
    ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C Γ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((k : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
            Qd.eval ((N : ℂ) ^ (-s)) := by sorry
