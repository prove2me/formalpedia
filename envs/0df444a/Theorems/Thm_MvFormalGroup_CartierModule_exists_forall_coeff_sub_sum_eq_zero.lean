-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero
-- name    : MvFormalGroup.CartierModule.exists_forall_coeff_sub_sum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/22531d69-647d-5541-9de0-e872b1e96aaa
-- title:
--   Weight-adic convergence of sums in the Cartier module
-- statement:
--   Fix a prime $p$, a commutative ring $R$, a natural number $d$, and a $d$-dimensional multivariate formal group law $\Phi$ over $R$, i.e. a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant coefficients, linear coefficients given by the Kronecker delta in each of the two blocks, and the associativity identity; $\Phi$ is assumed commutative, that is, interchanging the two blocks of variables fixes each component. Elements of [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) are $d$-tuples $f_j$ of power series in variables $X_m$ indexed by $m \in \mathbb{N}$, with zero constant coefficient, satisfying $f_j$ substituted into the big Witt addition family $\mathrm{addFam}\,p\,R$ equals the $j$-th component of $\Phi$ evaluated at the two tuples obtained from $f$ by renaming $X_m$ to $X_{(0,m)}$ and to $X_{(1,m)}$ respectively; this module carries a subtraction. Assign to a finitely supported exponent $e : \mathbb{N} \to_{0} \mathbb{N}$ the weight $\sum_m e(m)\,p^{m}$. Given $t : \mathbb{N} \to$ `CartierModule p Φ` and $N : \mathbb{N} \to \mathbb{N}$ monotone and unbounded (for every $B$ there is $K$ with $B \le N K$), suppose that for all $k$, all components $j$ and all $e$ of weight $< N k$ the coefficient of $e$ in the $j$-th component of $t_k$ vanishes. Then there is an element $s$ of the Cartier module such that for every $K$, every $j$ and every $e$ of weight $< N K$, the coefficient of $e$ in the $j$-th component of $s - \sum_{k < K} t_k$ vanishes.
--
--   This is the completeness of the Cartier module of a commutative formal group law for the weight (equivalently $V$-adic) filtration: a series of elements whose weight-supports tend to infinity has a sum. It is used in the proof of [`MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt), where a Cartier-theoretic decomposition has to be summed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_forall_coeff_sub_sum_eq_zero
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (t : ℕ → MvFormalGroup.CartierModule p Φ) (N : ℕ → ℕ) (hN : Monotone N)
    (hN' : ∀ B : ℕ, ∃ K, B ≤ N K)
    (ht : ∀ (k : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N k → MvPowerSeries.coeff e ((t k).toPowerSeries j) = 0) :
    ∃ s : MvFormalGroup.CartierModule p Φ, ∀ (K : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N K →
        MvPowerSeries.coeff e ((s - ∑ k ∈ Finset.range K, t k).toPowerSeries j) = 0 := by sorry
