-- Prove2me | Theorems.Thm_MvFormalGroup_WittLaw_coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost
-- name    : MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/385e3f54-3ff7-5050-ae15-fbf08c898e4c
-- title:
--   Ghost read-out of Verschiebung, Frobenius and Teichmüller substitutions
-- statement:
--   Fix a prime $p$, a commutative ring $R$, a sequence $c : \mathbb{N} \to R$ and a power series $G \in R[[X_0, X_1, \dots]]$ in countably many variables. Assume that $G$ is supported on the pure $p$-power monomials with ghost coefficients: the coefficient of $G$ at the exponent $\mathrm{single}\,k\,(p^n)$, i.e. at the monomial $X_k^{p^n}$, equals $p^k\,c(k+n)$ for all $k, n$, and the coefficient of $G$ at any exponent $e \in \mathbb{N} \to_0 \mathbb{N}$ that is not of the form $\mathrm{single}\,k\,(p^n)$ is $0$. The conclusion is a conjunction of three such coefficientwise descriptions of substitutions into $G$. First, for [`MvFormalGroup.WittLaw.verFam R`](def/MvFormalGroup_CartierModule.html#L411), the family sending $0 \mapsto 0$ and $n+1 \mapsto X_n$, the substituted series has coefficient $p^k \cdot (p\,c(k+n+1))$ at $X_k^{p^n}$ and coefficient $0$ at every exponent not of that form. Second, for [`MvFormalGroup.WittLaw.frobPolyFam p R`](def/MvFormalGroup_CartierModuleIntVerschiebung.html#L119), whose $n$-th member is the $n$-th component of the Witt-vector Frobenius of the tautological Witt vector `xTaut p R`, viewed as a power series, the coefficient at $X_k^{p^n}$ is $p^k \cdot (\text{if } k+n = 0 \text{ then } 0 \text{ else } c(k+n-1))$, and all other coefficients vanish. Third, for every $a \in R$ and the family [`MvFormalGroup.WittLaw.teichFam p a`](def/MvFormalGroup_CartierModuleHomothety.html#L19) with $n$-th member $a^{p^n} \cdot X_n$, the coefficient at $X_k^{p^n}$ is $p^k \cdot (a^{p^{k+n}}\,c(k+n))$, and all other coefficients vanish.
--
--   This is the ghost-component computation for the Witt formal group: writing $G = \sum_N c_N w_N(X)$ for the ghost polynomials $w_N(X) = \sum_{k \le N} p^k X_k^{p^{N-k}}$, the three clauses say that substituting the Verschiebung, the integral Frobenius and the Teichmüller homothety $\langle a \rangle$ replaces the coefficient sequence $c$ by $N \mapsto p\,c_{N+1}$, by $N \mapsto c_{N-1}$ (zero in degree $0$) and by $N \mapsto a^{p^N} c_N$ respectively, each again of ghost shape. It is used in the construction of a $V$-basis for the Cartier module of a formal group law from its logarithm, in [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_WittLaw_coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    ((∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.verFam R) G) : R) = (p : R) ^ k * ((p : R) * c (k + n + 1))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.verFam R) G) : R) = 0)) ∧
    ((∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.frobPolyFam p R) G) : R) =
            (p : R) ^ k * (if k + n = 0 then 0 else c (k + n - 1))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.frobPolyFam p R) G) : R) = 0)) ∧
    (∀ a : R,
      (∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.teichFam p a) G) : R) = (p : R) ^ k * (a ^ p ^ (k + n) * c (k + n))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.teichFam p a) G) : R) = 0)) := by sorry
