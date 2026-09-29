-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
-- name    : NumberField.PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/3af30530-310c-5f22-9db0-10d6aa4b4986
-- title:
--   Sub-multiplicativity of local norm classes in a tower
-- statement:
--   Let $E \subseteq L \subseteq F$ be number fields (with $E$-algebra structures on $L$ and $F$ forming a scalar tower, and $F/E$, $L/E$, $F/L$ all Galois), let $w$ be a nonzero prime of $\mathcal{O}_F$, write $w_L$ for the prime of $\mathcal{O}_L$ under $w$, and assume the prime of $\mathcal{O}_E$ under $w$ coincides with the prime $v$ of $\mathcal{O}_E$ under $w_L$. For a Galois layer $K \subseteq K''$ and a prime $w''$ of $\mathcal{O}_{K''}$, `decomp` denotes the decomposition subgroup of $K'' \simeq_{\text{alg}[K]} K''$ attached to the valuation subring of the $w''$-adic valuation, and `adicCompletionSemialgHom` the canonical map from the completion of $K$ at $w'' \cap \mathcal{O}_K$ to the completion of $K''$ at $w''$, semilinear over $\mathrm{algebraMap}$. Given $n$ and a family $c : \mathrm{Fin}\,n \to (E_v)^\times$ such that every $a \in (E_v)^\times$ satisfies: for some $i$ and some $b \in (L_{w_L})^\times$, the finite product $\prod^{\mathrm{f}}_{\rho \in \mathrm{decomp}(L/E, w_L)} \rho \cdot b$ equals the image of $a\,(c_i)^{-1}$ in $L_{w_L}$; and given $m$ and $d : \mathrm{Fin}\,m \to (L_{w_L})^\times$ with the analogous property for the layer $L \subseteq F$ at $w$; then there exists $c' : \mathrm{Fin}(n\,m) \to (E_v)^\times$ such that every $a \in (E_v)^\times$ admits $k$ and $b \in (F_w)^\times$ with $\prod^{\mathrm{f}}_{\sigma \in \mathrm{decomp}(F/E, w)} \sigma \cdot b$ equal to the image of $a\,(c' k)^{-1}$ in $F_w$ under the map attached to the extension $\langle w, h\rangle$ of $v$.
--
--   This is the sub-multiplicativity of the index of the group of local norms in a tower of completions: if $(E_v)^\times$ is covered by $n$ cosets modulo norms from $L_{w_L}$ and $(L_{w_L})^\times$ by $m$ cosets modulo norms from $F_w$, then $(E_v)^\times$ is covered by $nm$ cosets modulo norms from $F_w$, with the norm realised here as the product of conjugates over the decomposition group. It feeds the induction on layers used by [`NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp`](thm.html#NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L] [IsGalois L F]
    (w : HeightOneSpectrum (𝓞 F))
    (h : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w))
    (n : ℕ) (c : Fin n → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ)
    (hc : ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∃ (i : Fin n) (b : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ),
        (((∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • b :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom E L
            (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))
            ((a * (c i)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E))
    (m : ℕ) (d : Fin m → ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ)
    (hd : ∀ a' : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ,
      ∃ (j : Fin m) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ τ : ↥(NumberField.PlaceDecomp.decomp L F w), τ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
            (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))
            ((a' * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
              (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :
    ∃ c' : Fin (n * m) → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
        ∃ (k : Fin (n * m)) (b : (w.adicCompletion F)ˣ),
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
              (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))
              ((a * (c' k)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
                (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) := by sorry
