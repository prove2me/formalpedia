-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
-- name    : NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/cab252cf-75e1-5818-a4d6-b7118beb46f2
-- title:
--   Smooth periodic box-supported window in log-moduli and angle slots
-- statement:
--   Let $K$ be a number field, and write $r = \#\{\text{infinite places of } K\}$ and $r_2$ for the number of complex places, so that the mixed space is $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$. The data are: two maps $P_0, P_1 : (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,r_2 \to \mathbb{R}) \to \mathrm{mixedSpace}\,K$ with $P_0$ smooth ($C^\infty$ over $\mathbb{R}$), $P_0(x, \theta + k) = P_0(x,\theta)$ for every integer vector $k \in \mathbb{Z}^{r_2}$, the multiplicativity $P_0(x+x', \theta+\theta') = P_0(x,\theta)\cdot P_1(x',\theta')$, and the boundedness property that for every compact set $C$ in the mixed space all of whose points are units there is $R$ with $|x_i| \le R$ for all $i$ whenever $P_0(x,\theta) \in C$; a smooth $W_a : \mathrm{mixedSpace}\,K \to \mathbb{C}$ together with a compact set $C_0$ consisting of units such that $W_a$ vanishes outside $C_0$; natural numbers $c, d$, slot maps $\mathrm{cs} : \mathrm{Fin}\,r_2 \to \mathrm{Fin}\,d$ and $\mathrm{ts} : \mathrm{Fin}\,c \to \mathrm{Fin}\,d$, nonzero complex numbers $t_j$ ($j \in \mathrm{Fin}\,c$), an $\mathbb{R}$-linear form $\ell$ on $\mathrm{Fin}\,r \to \mathbb{R}$, and base points $x_0 \in \mathbb{R}^r$, $\theta_0 \in \mathbb{R}^{r_2}$, $n_0 \in \mathbb{Z}^c$. The conclusion asserts the existence of a map $G : (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,d \to \mathbb{R}) \to \mathbb{C}$ which is smooth, vanishes at every $p$ with $|p_1(i)| > R_b$ for some $i$, for some constant $R_b \ge 0$, is invariant under adding $1$ to any single one of the $d$ angle coordinates, and satisfies $$G(x_0 + x, \Theta) = \Big(\prod_j t_j^{-(n_{0,j} + k_j)}\Big)\, W_a\big(P_0(x_0,\theta_0)\cdot P_1(x,\theta)\big)$$ for all $x \in \mathbb{R}^r$, $\theta \in \mathbb{R}^{r_2}$, $k \in \mathbb{Z}^c$ and $\Theta \in \mathbb{R}^d$ such that $\Theta_{\mathrm{cs}(j)} \equiv \theta_j \pmod 1$ for all $j$, $\Theta_{\mathrm{ts}(j)} \equiv -k_j \arg(t_j)/(2\pi) \pmod 1$ for all $j$ (congruences taken in $\mathrm{AddCircle}\,1$), and $e^{\ell(x)} = \prod_j \|t_j\|^{-k_j}$.
--
--   This is the coordinate-change step which repackages an archimedean window on the units of the mixed space, twisted by the tilt factors $t_j^{-k_j}$, as a single smooth function of log-moduli and of $d$ angle variables that is $1$-periodic in each angle and compactly supported in the log-moduli directions; it is the shape needed before Fourier expansion in the angles. It feeds the polar-coordinate window constructions and the subsequent passage from sums over units to sums over a lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P₀ P₁ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (hP₀ : ContDiff ℝ (⊤ : ℕ∞) P₀)
    (hP₀_per : ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
      (k : Fin (nrComplexPlaces K) → ℤ), P₀ (x, θ + fun j => (k j : ℝ)) = P₀ (x, θ))
    (hP_mul : ∀ (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P₀ (x + x', θ + θ') = P₀ (x, θ) * P₁ (x', θ'))
    (hP₀_bdd : ∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
      ∃ R : ℝ, ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
        P₀ (x, θ) ∈ C → ∀ i, |x i| ≤ R)
    (Wa : mixedSpace K → ℂ) (hWa : ContDiff ℝ (⊤ : ℕ∞) Wa)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y)
    (hWa0 : ∀ y, Wa y ≠ 0 → y ∈ C₀)
    {c d : ℕ} (cs : Fin (nrComplexPlaces K) → Fin d) (ts : Fin c → Fin d)
    (t : Fin c → ℂ) (ht : ∀ j, t j ≠ 0)
    (ℓ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ)
    (x₀ : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ₀ : Fin (nrComplexPlaces K) → ℝ) (n₀ : Fin c → ℤ) :
    ∃ G : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧
        ∀ p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ), (∃ i, Rb < |p.1 i|) → G p = 0) ∧
      (∀ (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ)) (J : Fin d),
        G (p.1, p.2 + Pi.single J 1) = G p) ∧
      ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (k : Fin c → ℤ)
        (Θ : Fin d → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖t j‖ ^ (-(k j)) →
        G (x₀ + x, Θ) = (∏ j, t j ^ (-(n₀ j + k j))) * Wa (P₀ (x₀, θ₀) * P₁ (x, θ)) := by sorry
