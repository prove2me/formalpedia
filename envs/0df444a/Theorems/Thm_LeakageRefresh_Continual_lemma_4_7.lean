-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_7
-- name    : LeakageRefresh.Continual.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:17.131529+00:00
-- url     : https://prove2.me/theorems/35e09e47-6a68-44b0-98fb-ba75ab691518
-- title:
--   Lemma 4.7 — Gram variance for an invertible refresh: exact identity (4.21) and bound $\le\frac1{q-1}\mathbb E\|g_\ell(\ell')\|^2$ (4.22), rows and columns
-- statement:
--   Let $n\ge2$, $q=2^n-1$, and let $V$ be a finite-dimensional real inner-product space. For each $\ell\in U_L$ let $g_\ell:U_L\to V$, and put $\bar g_\ell=\mathbb E_{\ell'}[g_\ell(\ell')]$, $\hat g_\ell(\ell')=g_\ell(\ell')-\bar g_\ell$ and $Y_M=\frac1q\sum_{\ell\in U_L}g_\ell(\ell\cdot M)$. For independent uniform $M,M'\in\mathrm{InvMatr}^n_2$,
--   $$\mathbb E_M\big\|Y_M-\mathbb E_{M'}Y_{M'}\big\|^2=\frac{1}{q(q-1)}\sum_\ell\mathbb E_{\ell'}\|\hat g_\ell(\ell')\|^2-\frac{1}{q^2(q-1)}\mathbb E_{\ell'}\Big\|\sum_{\ell}\hat g_\ell(\ell')\Big\|^2, \tag{4.21}$$
--   $$\mathbb E_M\big\|Y_M-\mathbb E_{M'}Y_{M'}\big\|^2\le\frac{1}{q-1}\mathbb E_{\ell,\ell'}\|g_\ell(\ell')\|^2. \tag{4.22}$$
--   All averages over $\ell,\ell'$ are uniform on $U_L$. The same holds for columns: for $g_r:U_R\to V$ ($r\in U_R$) and $Y_M=\frac1q\sum_r g_r(M^{-1}r)$. This controls the Gram matrices of singular functions restricted along a random refresh.
--
--   Differences from the source:
--   - encoding: $\mathbb E_M$, $\mathbb E_{M'}$, $\mathbb E_{\ell'}$ over uniform sets → `avg` over `InvMatr n`, `UL n`, `UL n × UL n` and normalized sums; reason: uniform expectations on finite sets
--   - encoding: "the same statement holds for column images under $M^{-1}$" → a second conjunct with $g_r:U_R\to V$ and $Y_M=q^{-1}\sum_r g_r(M^{-1}r)$; reason: the column version stated explicitly
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), pp. 33–34, Lemma 4.7

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_Tables

namespace LeakageRefresh.Continual

/-- **Lemma 4.7 (Gram variance for an invertible refresh).** For a finite-dimensional real
inner-product space `V`, maps `g_ℓ : U_L → V` (`ℓ ∈ U_L`), `ḡ_ℓ = E_{ℓ′}[g_ℓ(ℓ′)]`,
`ĝ_ℓ = g_ℓ − ḡ_ℓ`, `Y_M = q⁻¹ ∑_ℓ g_ℓ(ℓ · M)` and `M, M′ ←$ InvMatr`:
(4.21) `E_M‖Y_M − E_{M′}Y_{M′}‖² = 1/(q(q−1)) ∑_ℓ E_{ℓ′}‖ĝ_ℓ(ℓ′)‖² − 1/(q²(q−1)) E_{ℓ′}‖∑_ℓ ĝ_ℓ(ℓ′)‖²`,
(4.22) `E_M‖Y_M − E_{M′}Y_{M′}‖² ≤ 1/(q−1) E_{ℓ,ℓ′}‖g_ℓ(ℓ′)‖²`;
and the same for columns, `Y_M = q⁻¹ ∑_r g_r(M⁻¹ · r)`. -/
theorem lemma_4_7 (n : ℕ) (hn : 2 ≤ n) {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    (∀ g : UL n → UL n → V,
      let q : ℝ := (2 : ℝ) ^ n - 1
      let gbar : UL n → V := fun ℓ => (Fintype.card (UL n) : ℝ)⁻¹ • ∑ ℓ', g ℓ ℓ'
      let ghat : UL n → UL n → V := fun ℓ ℓ' => g ℓ ℓ' - gbar ℓ
      let Y : InvMatr n → V := fun M => q⁻¹ • ∑ ℓ, g ℓ (refreshL M ℓ)
      let Ybar : V := (Fintype.card (InvMatr n) : ℝ)⁻¹ • ∑ M', Y M'
      avg (fun M => ‖Y M - Ybar‖ ^ 2) =
          1 / (q * (q - 1)) * ∑ ℓ, avg (fun ℓ' => ‖ghat ℓ ℓ'‖ ^ 2) -
            1 / (q ^ 2 * (q - 1)) * avg (fun ℓ' => ‖∑ ℓ, ghat ℓ ℓ'‖ ^ 2) ∧
        avg (fun M => ‖Y M - Ybar‖ ^ 2) ≤
          1 / (q - 1) * avg (fun p : UL n × UL n => ‖g p.1 p.2‖ ^ 2)) ∧
    (∀ g : UR n → UR n → V,
      let q : ℝ := (2 : ℝ) ^ n - 1
      let gbar : UR n → V := fun r => (Fintype.card (UR n) : ℝ)⁻¹ • ∑ r', g r r'
      let ghat : UR n → UR n → V := fun r r' => g r r' - gbar r
      let Y : InvMatr n → V := fun M => q⁻¹ • ∑ r, g r (refreshR M r)
      let Ybar : V := (Fintype.card (InvMatr n) : ℝ)⁻¹ • ∑ M', Y M'
      avg (fun M => ‖Y M - Ybar‖ ^ 2) =
          1 / (q * (q - 1)) * ∑ r, avg (fun r' => ‖ghat r r'‖ ^ 2) -
            1 / (q ^ 2 * (q - 1)) * avg (fun r' => ‖∑ r, ghat r r'‖ ^ 2) ∧
        avg (fun M => ‖Y M - Ybar‖ ^ 2) ≤
          1 / (q - 1) * avg (fun p : UR n × UR n => ‖g p.1 p.2‖ ^ 2)) := by sorry

end LeakageRefresh.Continual
