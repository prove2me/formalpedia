-- Prove2me | Theorems.Thm_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
-- name    : NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c7dbc41c-7463-5fea-9403-220549684924
-- title:
--   Folded archimedean discrepancy window over the S-part idele measure
-- statement:
--   Let $K$ be a number field, let the unit group $(\mathbb{A}_K)^\times$ of the adele ring `AdeleRing (𝓞 K) K` carry a measurable structure which is the Borel structure of its topology, and let $\nu_{ZK}$ be a Haar measure on it. Let $S_K$ be a finite set of height-one primes of $\mathcal{O}_K$, and let $\xi$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that the associated function $z \mapsto \xi(z)$ on $(\mathbb{A}_K)^\times$ is continuous (hypothesis `hξc`).
--
--   Archimedean data: a function $B_d$ on pairs of points of the Minkowski space `mixedEmbedding.mixedSpace K` (pairs being indexed by `Fin 2`) and, for each infinite place $w$ of $K$, functions $C_d(w)$, $E_d(w)$ on such pairs, all complex valued. The hypotheses `hBd_smooth`, `hCd_smooth`, `hEd_smooth` say that $B_d$ and each $C_d(w)$, $E_d(w)$ are $C^\infty$ over $\mathbb{R}$, and `hBd_cs`, `hCd_cs`, `hEd_cs` say that each of them has compact support. Further, $C_{aD}$ is a set of pairs of units of the infinite adele ring, assumed compact (`hCaD`), and the hypothesis `hBCE_Ca` requires that every point $p$ of $\operatorname{tsupport} B_d \cup \bigcup_w (\operatorname{tsupport} C_d(w) \cup \operatorname{tsupport} E_d(w))$ be of the form $p = [\,\mu(q_1),\ \mu(q_2)\,]$ for some $(q_1,q_2) \in C_{aD}$, where $\mu =$ `InfiniteAdeleRing.ringEquiv_mixedSpace K` identifies the infinite adele ring with the Minkowski space; that is, both coordinates of any support point come from a fixed compact set of pairs of archimedean units.
--
--   Finite data: for each height-one prime $v$ a function $\Phi_f(v)$ on pairs of elements of the completion $K_v$, subject to the hypothesis `hΦf`: for every $v \in S_K$, $\Phi_f(v)$ is locally constant, has compact support, and vanishes whenever either coordinate of its argument is $0$.
--
--   Throughout, $\mu_{S_K}$ denotes the measure obtained by restricting $\nu_{ZK}$ to the subgroup [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) — the ideles $\delta$ such that for every prime $v \notin S_K$ both the finite component of $\delta$ at $v$ and that of $\delta^{-1}$ at $v$ lie in the valuation ring `v.adicCompletionIntegers K` — and then pushing it forward along [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90), the map induced on units by the ring homomorphism which keeps the archimedean component of an adele and replaces its finite component by its image under `truncFin K SK`.
--
--   For $w$ an infinite place write $m_w$ for `w.mult`, and for $x \in K$ write $x_w$ for the image of $x$ in the completion at $w$, obtained by taking the archimedean component `AdelicLevel.adeleArch` of $x$ viewed in the adele ring and then evaluating at $w$ by `AdelicLevel.archEval`.
--
--   The assertion is the existence of a function $B_t$ on (Minkowski space) $\times$ $\prod_v K_v$ and, for each infinite place $w$, functions $C_t(w)$, $E_t(w)$ on the same product, with complex values, such that the following five statements hold.
--
--   First: for every $b \in \prod_v K_v$, the function $y \mapsto B_t(y,b)$ is $C^\infty$ over $\mathbb{R}$ on the Minkowski space, and for every infinite place $w$ both $y \mapsto C_t(w,y,b)$ and $y \mapsto E_t(w,y,b)$ are $C^\infty$.
--
--   Second: there is a compact set $C_1$ in the Minkowski space all of whose elements are units, such that for every $y \notin C_1$ and every $b$ one has $B_t(y,b) = 0$ and $C_t(w,y,b) = E_t(w,y,b) = 0$ for all $w$.
--
--   Third: for every $y$ in the Minkowski space, the functions $b \mapsto B_t(y,b)$ and, for each $w$, $b \mapsto C_t(w,y,b)$ and $b \mapsto E_t(w,y,b)$ are locally constant.
--
--   Fourth: there is a family $C_f$ assigning to each height-one prime $v$ a subset of $K_v$, such that $C_f(v)$ is compact and does not contain $0$ for every $v \in S_K$, and such that whenever $b_v \notin C_f(v)$ for some $v \in S_K$, one has $B_t(y,b) = 0$ and $C_t(w,y,b) = E_t(w,y,b) = 0$ for all $w$, for every $y$.
--
--   Fifth: for every $u \in K^\times$ with $u \ne 1$ and every $b \in \prod_v K_v$, the function of $z \in (\mathbb{A}_K)^\times$ given by
--   $$\xi(z)\cdot \Lambda(u)\Big[ B_d\big[\mu((u^{-1})_\infty),\, \mu((zu)_\infty)\big] + \sum_{w\ \mathrm{real}} \|1-(u^{-1})_w\|\, C_d(w)\big[\mu((u^{-1})_\infty),\, \mu((zu)_\infty)\big] + \sum_{w\ \mathrm{complex}} \|1-(u^{-1})_w\|^2 \log\|1-(u^{-1})_w\|\, E_d(w)\big[\mu((u^{-1})_\infty),\, \mu((zu)_\infty)\big]\Big]\cdot \prod_{v \in S_K} \Phi_f(v)\big(b_v,\ z_v\big),$$
--   where the scalar is
--   $$\Lambda(u) = \Big(\prod_{w} \|u_w - 1\|^{m_w}\Big)\cdot\Big(\prod_{w} \big(\|1-(u^{-1})_w\|\,/\,\sqrt{\|(u^{-1})_w\|}\big)^{m_w}\Big)^{-1},$$
--   the sums over real and complex places being taken over the corresponding subsets of the infinite places, $(zu)_\infty$ denoting the archimedean component of the adele $z \cdot u$ and $z_v$ the value at $v$ of the finite component of $z$, is integrable with respect to $\mu_{S_K}$, and its integral against $\mu_{S_K}$ equals
--   $$B_t\big(\mu(u_\infty),\, b\big) + \sum_{w\ \mathrm{real}} \|1-(u^{-1})_w\|\, C_t\big(w, \mu(u_\infty), b\big) + \sum_{w\ \mathrm{complex}} \|1-(u^{-1})_w\|^2 \log\|1-(u^{-1})_w\|\, E_t\big(w, \mu(u_\infty), b\big).$$
--   Thus the archimedean and real/complex "kink" coefficients $\|1-(u^{-1})_w\|$ and $\|1-(u^{-1})_w\|^2\log\|1-(u^{-1})_w\|$ remain outside as explicit scalars, while the dependence on $u$ is absorbed into the values of $B_t, C_t(w), E_t(w)$ at the Minkowski image of $u$.
--
--   This is the folding step for the archimedean discrepancy window: the idelic integral of an archimedean window against finitely many locally constant local windows is rewritten, for each $u \in K^\times$ with $u \ne 1$, as values at the Minkowski image of $u$ of functions that are smooth in the archimedean variable, locally constant and compactly supported away from the axes in the finite variable, and supported in a compact set of units. It is used in the comparison of the two sides of the numerical identity [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le), and rests on the inverse-and-twist smoothness statement for windows on the Minkowski space together with the kink-window integral formula over the $S$-part idele measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Classical in

theorem NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Bd : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (Cd Ed : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hBd_smooth : ContDiff ℝ (⊤ : ℕ∞) Bd) (hCd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cd w))
    (hEd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ed w))
    (hBd_cs : HasCompactSupport Bd) (hCd_cs : ∀ w, HasCompactSupport (Cd w)) (hEd_cs : ∀ w, HasCompactSupport (Ed w))
    (CaD : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCaD : IsCompact CaD)
    (hBCE_Ca : ∀ p ∈ tsupport Bd ∪ ⋃ w, (tsupport (Cd w) ∪ tsupport (Ed w)),
      ∃ q ∈ CaD, p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)])
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ SK, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∃ (Bt : mixedEmbedding.mixedSpace K → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) → ℂ)
      (Ct Et : NumberField.InfinitePlace K → mixedEmbedding.mixedSpace K → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) → ℂ),
      (∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K, ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Bt y b) ∧
        ∀ w, ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Ct w y b) ∧ ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Et w y b)) ∧
      (∃ C₁ : Set (mixedEmbedding.mixedSpace K), IsCompact C₁ ∧ (∀ y ∈ C₁, IsUnit y) ∧
        ∀ (y : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), y ∉ C₁ → Bt y b = 0 ∧ ∀ w, Ct w y b = 0 ∧ Et w y b = 0) ∧
      (∀ y : mixedEmbedding.mixedSpace K, IsLocallyConstant (Bt y) ∧ ∀ w, IsLocallyConstant (Ct w y) ∧ IsLocallyConstant (Et w y)) ∧
      (∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K),
        (∀ v ∈ SK, IsCompact (Cf v) ∧ (0 : v.adicCompletion K) ∉ Cf v) ∧
        ∀ (y : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), (∃ v ∈ SK, b v ∉ Cf v) →
          Bt y b = 0 ∧ ∀ w, Ct w y b = 0 ∧ Et w y b = 0) ∧
      ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K,
        Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
          (Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) ∧
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        Bt (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ct w (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Et w (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b := by sorry
