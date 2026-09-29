-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
-- name    : NumberField.mixedEmbedding.exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/152060a2-1cc8-5d08-9616-315983997364
-- title:
--   Kink-basis windows from exponential–polar coordinates
-- statement:
--   Let $K$ be a number field, let $r$ be the number of infinite places and $r_2$ the number of complex places. Let $P_0,P_1\colon(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,r_2\to\mathbb R)\to \mathrm{mixedSpace}\,K$ be maps with $P_0$ smooth, invariant under integral translations of the angle variables, satisfying $P_0(x+x',\theta+\theta')=P_0(x,\theta)\,P_1(x',\theta')$, and such that for every compact set $C$ consisting of units of the mixed space there is an $R$ with $|x_i|\le R$ for all $i$ whenever $P_0(x,\theta)\in C$. Let $C_0$ be a compact set all of whose elements are units, let $c,d\in\mathbb N$, let $cs\colon\mathrm{Fin}\,r_2\to\mathrm{Fin}\,d$ and $ts\colon\mathrm{Fin}\,c\to\mathrm{Fin}\,d$ be index maps, $t\colon\mathrm{Fin}\,c\to\mathbb C$ with all $t_j\ne0$, $\ell$ a real linear form on $\mathrm{Fin}\,r\to\mathbb R$, $x_0$ a base point and $n_0\colon\mathrm{Fin}\,c\to\mathbb Z$. Let $\iota_w$ attach to each infinite place an $x$-index, $s$ attach a unit of $\mathbb Z$ to each real place, and $cw$ be an injection of the complex places into $\mathrm{Fin}\,d$; let $w_R\colon\mathrm{Fin}\,q\simeq\{\text{real places}\}$ with $k_R(k)=\iota_w(w_R(k))$, and let $k_C\colon\mathrm{Fin}\,d\to\mathrm{Fin}\,r$ satisfy $k_C(cw(w))=\iota_w(w)$ for every complex place $w$. Finally let $W_B$ and the families $W_{C,w},W_{E,w}$ ($w$ an infinite place) be smooth $\mathbb C$-valued functions on the mixed space, each vanishing at every point outside $C_0$. The assertion is that there exist functions $B$, $C_{k}$ ($k<q$) and $E_j$ ($j<d$) on $(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,d\to\mathbb R)$, all smooth, all unchanged under $\Theta\mapsto\Theta+e_J$ for each coordinate $J$, and a real $R_b\ge 0$ such that all of them vanish at any $(x,\Theta)$ with $|x_i|>R_b$ for some $i$, and such that for all $x$, $\theta$, $k\in\mathbb Z^{c}$ and $\Theta$ satisfying $\Theta_{cs(j)}\equiv\theta_j$ and $\Theta_{ts(j)}\equiv-k_j\arg(t_j)/2\pi$ in $\mathbb R/\mathbb Z$ and $e^{\ell(x)}=\prod_j\|t_j\|^{-k_j}$, one has, writing $X=x_0+x$ and $y=P_0(x_0,0)\,P_1(x,\theta)$, $$B(X,\Theta)+\sum_{k'<q}\bigl|1-e^{X_{k_R(k')}}\bigr|\,C_{k'}(X,\Theta)+\sum_{j<d}\|1-v_j\|^{2}\log\|1-v_j\|\,E_j(X,\Theta)=\Bigl(\prod_j t_j^{-(n_{0,j}+k_j)}\Bigr)\Bigl(W_B(y)+\sum_{w\ \mathrm{real}}\varepsilon_w W_{C,w}(y)+\sum_{w\ \mathrm{complex}}\eta_w W_{E,w}(y)\Bigr),$$ where $v_j=e^{X_{k_C(j)}/2+2\pi i\Theta_j}$, $\varepsilon_w=e^{-X_{\iota_w(w)}}|1-e^{X_{\iota_w(w)}}|$ if $s_w=1$ and $\varepsilon_w=1+e^{-X_{\iota_w(w)}}$ otherwise, and $\eta_w=e^{-X_{\iota_w(w)}}\bigl(\|1-u_w\|^{2}\log\|1-u_w\|-\tfrac{1}{2}X_{\iota_w(w)}\|1-u_w\|^{2}\bigr)$ with $u_w=e^{X_{\iota_w(w)}/2+2\pi i\Theta_{cw(w)}}$; the real-valued coefficients are coerced into $\mathbb C$.
--
--   This is the archimedean "kink window" companion of [`NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord`](thm.html#NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord), which the proof cites: windows supported on a compact set of units of the mixed space, transported through exponential–polar coordinates with base angle $0$, are repackaged as smooth, box-supported, angle-periodic windows paired with the kink functions $|1-e^{x}|$ and $\|1-e^{x/2+2\pi i\Theta}\|^{2}\log\|1-e^{x/2+2\pi i\Theta}\|$. It feeds the unit-sum comparison [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P₀ P₁ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (hP₀ : ContDiff ℝ (⊤ : ℕ∞) P₀)
    (hP₀_per : ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ)
      (k : Fin (nrComplexPlaces K) → ℤ), P₀ (x, θ + fun j => (k j : ℝ)) = P₀ (x, θ))
    (hP_mul : ∀ (x x' : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P₀ (x + x', θ + θ') = P₀ (x, θ) * P₁ (x', θ'))
    (hP₀_bdd : ∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
      ∃ R : ℝ, ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ),
        P₀ (x, θ) ∈ C → ∀ i, |x i| ≤ R)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y)
    {c d : ℕ} (cs : Fin (nrComplexPlaces K) → Fin d) (ts : Fin c → Fin d)
    (t : Fin c → ℂ) (ht : ∀ j, t j ≠ 0)
    (ℓ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ)
    (x₀ : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (n₀ : Fin c → ℤ)

    (ιw : InfinitePlace K → Fin (Fintype.card (InfinitePlace K)))
    (s : {w : InfinitePlace K // w.IsReal} → ℤˣ)
    (cw : {w : InfinitePlace K // w.IsComplex} → Fin d) (hcw : Function.Injective cw)

    {q : ℕ} (wR : Fin q ≃ {w : InfinitePlace K // w.IsReal})
    (kR : Fin q → Fin (Fintype.card (InfinitePlace K))) (hkR : ∀ k, kR k = ιw (wR k).1)
    (kC : Fin d → Fin (Fintype.card (InfinitePlace K)))
    (hkC : ∀ w : {w : InfinitePlace K // w.IsComplex}, kC (cw w) = ιw w.1)

    (WB : mixedSpace K → ℂ) (hWB : ContDiff ℝ (⊤ : ℕ∞) WB) (hWB0 : ∀ y, WB y ≠ 0 → y ∈ C₀)
    (WC : InfinitePlace K → mixedSpace K → ℂ) (hWC : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (WC w))
    (hWC0 : ∀ w y, WC w y ≠ 0 → y ∈ C₀)
    (WE : InfinitePlace K → mixedSpace K → ℂ) (hWE : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (WE w))
    (hWE0 : ∀ w y, WE w y ≠ 0 → y ∈ C₀) :
    ∃ (Bw : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ) (Cw : Fin q → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ) (Ew : Fin d → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ),
      (ContDiff ℝ (⊤ : ℕ∞) Bw ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Cw k)) ∧ ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ew j)) ∧
      (∀ (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ)) (J : Fin d),
        Bw (p.1, p.2 + Pi.single J 1) = Bw p ∧ (∀ k, Cw k (p.1, p.2 + Pi.single J 1) = Cw k p) ∧
          ∀ j, Ew j (p.1, p.2 + Pi.single J 1) = Ew j p) ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧ ∀ p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ), (∃ i, Rb < |p.1 i|) →
        Bw p = 0 ∧ (∀ k, Cw k p = 0) ∧ ∀ j, Ew j p = 0) ∧
      ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ) (k : Fin c → ℤ) (Θ : (Fin d → ℝ)),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖t j‖ ^ (-(k j)) →
        Bw (x₀ + x, Θ) +
            ∑ k' : Fin q, ((|1 - Real.exp ((x₀ + x) (kR k'))| : ℝ) : ℂ) * Cw k' (x₀ + x, Θ) +
            ∑ j : Fin d, ((‖(1 : ℂ) - Complex.exp ((((x₀ + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ ^ 2 *
                Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              Ew j (x₀ + x, Θ) =
          (∏ j, t j ^ (-(n₀ j + k j))) *
            (WB (P₀ (x₀, 0) * P₁ (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal),
                ((if hw : w.IsReal then
                    (if s ⟨w, hw⟩ = 1 then
                        Real.exp (-((x₀ + x) (ιw w))) * |1 - Real.exp ((x₀ + x) (ιw w))|
                      else 1 + Real.exp (-((x₀ + x) (ιw w))))
                  else 0 : ℝ) : ℂ) * WC w (P₀ (x₀, 0) * P₁ (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                ((if hw : w.IsComplex then
                    Real.exp (-((x₀ + x) (ιw w))) *
                      (‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2 *
                          Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ -
                        (x₀ + x) (ιw w) / 2 *
                          ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2)
                  else 0 : ℝ) : ℂ) * WE w (P₀ (x₀, 0) * P₁ (x, θ))) := by sorry
