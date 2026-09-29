-- Prove2me | Theorems.Thm_MvPowerSeries_exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation
-- name    : MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/254373a3-e01a-5111-8f48-9c45f2d0be44
-- title:
--   Hazewinkel functional-equation lemma: integrality of Theta
-- statement:
--   Fix a prime $p$, an integer $d \ge 0$ and an arbitrary index type $\tau$, and write $K = \mathbb{Q}_p[V_{m,i,j}]$ for the polynomial ring `MvPolynomial (ℕ × Fin d × Fin d) (Padic p)` over the $p$-adic field, $A = \mathbb{Z}_p[V_{m,i,j}]$ for the corresponding polynomial ring over `PadicInt p`, and $\sigma$ for the $\mathbb{Q}_p$-algebra endomorphism of $K$ sending each variable $v$ to $v^p$. Let $a : \mathbb{N} \to M_d(K)$ satisfy $a_0 = 1$ and the functional equation $p \cdot a_{k+1} = \sum_{m=0}^{k} \bigl(V_{m,i,j}\bigr)_{i,j} \cdot \sigma^{m+1}(a_{k-m})$ for all $k$, where $\sigma^{m+1}$ acts entrywise and $\bigl(V_{m,i,j}\bigr)_{i,j}$ is the matrix of variables with first index $m$. Let $f : \mathrm{Fin}\,d \to K[[X_1,\dots,X_d]]$ have coefficient $a_k{}_{ij}$ at the monomial $X_j^{p^k}$ for all $i,j,k$, and coefficient $0$ at every exponent vector that is not of the form $p^k$ times a single basis vector. Let $\Theta : \mathrm{Fin}\,d \to K[[X_t : t \in \tau]]$ have zero constant coefficient in each component, let $g : \mathrm{Fin}\,d \to K[[X_t : t \in \tau]]$, and assume $g_i$ is the substitution of $\Theta$ into $f_i$ for each $i$. Assume further that for every $i$ and every exponent $e : \tau \to_0 \mathbb{N}$ there is $r \in A$ with
--   $$p \cdot (g_i)_e - \sum_{m < \deg e} \sum_{l} V_{m,i,l} \cdot \Bigl(\bigl(\sigma^{m+1} g_l\bigr)(X^{p^{m+1}})\Bigr)_e = p \cdot \iota(r),$$
--   where $\sigma^{m+1}$ acts on coefficients, the inner substitution $X_t \mapsto X_t^{p^{m+1}}$ is `MvPowerSeries.expand`, $\deg e$ is the total degree of $e$, and $\iota : A \to K$ is induced by $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$. Then there are power series $\Theta_{0,i} \in A[[X_t : t \in \tau]]$ whose images under $\iota$ applied coefficientwise are the $\Theta_i$; that is, every coefficient of every $\Theta_i$ lies in $A$.
--
--   This is the integrality half of Hazewinkel's functional-equation lemma, in the universal $p$-typical setting: the twists $V_{m,i,j}$ are indeterminates, $f$ is the $p$-typical logarithm attached to $a$, and the hypothesis on $g = f(\Theta)$ is the functional-equation congruence for the same twists. The statement takes $\Theta$ with $f(\Theta) = g$ as given, rather than constructing it, and is used in the Cartier-module treatment of multivariate formal groups, where it supplies the integral descent step in [`MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation`](thm.html#MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation
    (p : ℕ) [Fact p.Prime] (d : ℕ) {τ : Type u}
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (Θ : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (hΘ : ∀ i, (Θ i).constantCoeff = 0)
    (g : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (hfg : ∀ i, MvPowerSeries.subst Θ (f i) = g i)
    (hFE : ∀ (i : Fin d) (e : τ →₀ ℕ), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * (g i).coeff e
        - ∑ m ∈ Finset.range (Finsupp.degree e), ∑ l : Fin d,
            MvPolynomial.X (m, i, l) *
              (MvPowerSeries.expand (p ^ (m + 1)) (pow_ne_zero (m + 1) (Fact.out : p.Prime).ne_zero)
                (MvPowerSeries.map
                  ((MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p]
                        MvPolynomial (ℕ × Fin d × Fin d) (Padic p)).toRingHom ^ (m + 1)) (g l))).coeff e
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
            * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r) :
    ∃ Θ₀ : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)),
      ∀ i, MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) (Θ₀ i) = Θ i := by sorry
