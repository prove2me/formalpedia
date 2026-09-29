-- Prove2me | Theorems.Thm_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
-- name    : NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7eb87b63-a1a6-52c1-b543-15bc4ee7536f
-- title:
--   Discrepancy-window class sums as summable lattice sums of kink windows
-- statement:
--   Fix a number field $K$, write $r = \#\{\text{infinite places of }K\}$ and let $\nu_{Z_K}$ be a Haar measure on the idele unit group $(\mathbb{A}_K^{\times})$, i.e. on $(\mathrm{AdeleRing}\,(\mathcal{O}_K)\,K)^{\times}$ with its Borel structure.
--
--   **Character data.** $\Xi$ is a finite set of monoid homomorphisms from the top subgroup of $(\mathbb{A}_K)^{\times}$ to $\mathbb{C}^{\times}$. The hypothesis `hΞc` asks that for each $\xi \in \Xi$ the function $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function on $(\mathbb{A}_K)^{\times}$, and `hΞt` that each $\xi$ is trivial on the image of $K^{\times}$ under the principal-idele map.
--
--   **Places and tilt data.** $S_K$ and $T$ are finite sets of height-one primes of $\mathcal{O}_K$ with $T$ disjoint from $S_K$ (`hTS`) and $2 \le \#T$ (`hT2`). The hypothesis `hur` asks that for $\xi \in \Xi$, every $v \notin S_K$ and every unit $t$ of $K_v$ with $\mathrm{v}(t) = 1$, the value of $\xi$ at the idele which is $t$ at $v$ and $1$ at all other finite places and at the infinite places (the image of $t$ under `localUnit` followed by `finIncl`) equals $1$. Further data: weights $f : \{\text{primes}\} \to \mathbb{N}$ with $f v > 0$ for $v \in T$ (`hf`); natural numbers $N_v$ with $N_v = \mathrm{absNorm}(v)^{f v}$ for $v \in T$ (`hNwf`); complex numbers $\zeta_v, s_v$ with $\zeta_v \ne 0$ and $s_v^2 = \zeta_v$ for $v \in T$ (`hζ`, `hs`); and the eigenvalue normalisation `hx`: for every $\xi \in \Xi$ and $v \in T$, $\xi(\det (\mathtt{heckeGen}\,(\mathcal{O}_K)\,K\,v))^{f v} = \zeta_v$, where $\mathtt{heckeGen}$ is the $\mathrm{GL}_2$-element built from the uniformizer unit at $v$.
--
--   **Plain windows.** $\Phi_a$ is a $\mathbb{C}$-valued function on pairs of points of the mixed space of $K$ (functions on $\mathrm{Fin}\,2$), assumed smooth (`hΦa_smooth`), of compact support (`hΦa_cs`), vanishing unless both entries correspond to units of the infinite adele ring under the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace` (`hΦa_units`), and with $\mathrm{tsupport}\,\Phi_a$ contained in the image of a compact set $C_a$ of pairs of infinite-adele units (`hCa`, `hΦa_Ca`). For each finite place $v$, $\Phi_{f,v}$ is a function on $K_v \times K_v$, and `hΦf` asks that for $v \in S_K$ it be locally constant, compactly supported, and vanish unless both coordinates are nonzero.
--
--   **Archimedean discrepancy coefficients.** $B_d$ and, indexed by infinite places $w$, $C_{d,w}$ and $E_{d,w}$ are functions on pairs of mixed-space points, all smooth (`hBd_smooth`, `hCd_smooth`, `hEd_smooth`) and compactly supported (`hBd_cs`, `hCd_cs`, `hEd_cs`); `hBCE_units` asks that at any point where $B_d$ or some $C_{d,w}$ or $E_{d,w}$ is nonzero both entries come from units of the infinite adele ring; and `hBCE_Ca` asks that $\mathrm{tsupport}\,B_d \cup \bigcup_w (\mathrm{tsupport}\,C_{d,w} \cup \mathrm{tsupport}\,E_{d,w})$ lie in the image of a compact set $C_{aD}$ of pairs of infinite-adele units (`hCaD`).
--
--   **Local discrepancy windows.** For each finite place $v$, $\Psi_{f,v}$ is a function on pairs of units of $K_v$. For $v \in S_K$ four conditions are imposed: compact support (`hΨf_cs`); local constancy away from $t = 1$ (`hΨf_lc`: at each pair $p$ with $p_2 \ne 1$ there is a neighbourhood of $p$ on which $\Psi_{f,v}$ is constant); a uniform multiplicative cell structure near $t = 1$ (`hΨf_cells`: there are a neighbourhood $U$ of $1$ in $K_v^{\times}$ and $\rho > 0$ such that $\Psi_{f,v}(a',t') = \Psi_{f,v}(a,t)$ whenever $t \in U$, $\|a' - a\| \le \rho\|a\|$ and $\|t' - t\| \le \rho\|1-t\|$); and a logarithmic germ bound (`hΨf_germ`: there is $C$ with $\|\Psi_{f,v}(a,t) - \Psi_{f,v}(a,1)\| \le C\,\|1-t\|\,(1 + |\log\|1-t\||)$ for all units $a,t$).
--
--   Finally, $C$ and $c'$ are arbitrary complex numbers.
--
--   **Conclusion.** There exist natural numbers $A$ and $q$ and an additive subgroup $\Lambda$ of $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,\#T \to \mathbb{Z})$ carrying the discrete topology, such that all of the following hold.
--
--   (i) There are an $\mathbb{R}$-linear functional $sl$ on $\mathrm{Fin}\,r \to \mathbb{R}$ and a nonzero $\omega : \mathrm{Fin}\,\#T \to \mathbb{R}$ with $sl(\gamma_1) = \sum_i \omega_i \gamma_2(i)$ for every $\gamma \in \Lambda$.
--
--   (ii) There are an additive homomorphism $\chi$ from $\Lambda$ to $\mathrm{Fin}(r + \#T) \to \mathbb{R}/\mathbb{Z}$ and a function $\mathrm{lift}$ on all of $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,\#T \to \mathbb{Z})$ with values in $\mathrm{Fin}(r + \#T) \to \mathbb{R}$, such that for $\gamma \in \Lambda$ and each coordinate $j$ the class of $\mathrm{lift}(\gamma)(j)$ in $\mathbb{R}/\mathbb{Z}$ is $\chi(\gamma)(j)$.
--
--   (iii) There are index maps $kC : \mathrm{Fin}(r+\#T) \to \mathrm{Fin}\,r$ and $kR : \mathrm{Fin}\,q \to \mathrm{Fin}\,r$ and finitely many shapes $B_w(a)$, $C_w(a,k)$, $E_w(a,j)$ (for $a \in \mathrm{Fin}\,A$, $k \in \mathrm{Fin}\,q$, $j \in \mathrm{Fin}(r+\#T)$), all $\mathbb{C}$-valued functions on $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}(r+\#T) \to \mathbb{R})$, all smooth, and all invariant under adding $1$ to any single angular coordinate: for all $a$, all $p$ and all $j$, $B_w(a)(p_1, p_2 + e_j) = B_w(a)(p)$, $C_w(a,k)(p_1,p_2+e_j) = C_w(a,k)(p)$ for every $k$, and $E_w(a,j')(p_1,p_2+e_j) = E_w(a,j')(p)$ for every $j'$.
--
--   (iv) There is a compact set $S_x \subseteq (\mathrm{Fin}\,r \to \mathbb{R})$ such that for every shape index and every $p$ with $p_1 \notin S_x$ the values $B_w(a)(p)$, $C_w(a,k)(p)$ and $E_w(a,j)(p)$ all vanish.
--
--   (v) There are a sequence of additive subgroups $\mathrm{sub}(i) \le \Lambda$ ($i \in \mathbb{N}$), a shape assignment $\mathrm{shape} : \mathbb{N} \to \mathrm{Fin}\,A$, coefficients $\mathrm{lam} : \mathbb{N} \to \mathbb{C}$ with $\sum_i \|\mathrm{lam}(i)\| < \infty$, and offsets $x_0(i) \in (\mathrm{Fin}\,r \to \mathbb{R})$, $n_0(i) \in (\mathrm{Fin}\,\#T \to \mathbb{Z})$, $\theta_0(i) \in (\mathrm{Fin}(r+\#T) \to \mathbb{R})$, such that for every $n : \mathrm{Fin}\,\#T \to \mathbb{Z}$ the following identity holds.
--
--   On the left-hand side stands $C$ times the finite sum (`finsum`) over those $u \in K^{\times}$ with $u \ne 1$, with $\mathrm{ord}_v$ of the principal idele of $u$ equal to $0$ for every $v \notin S_K \cup T$, and with $\mathrm{ord}_{v_i}$ of that idele equal to $f(v_i)\,n(i)$ for each $i$, where $v_i$ is the $i$-th prime of $T$ under `T.equivFin` and $\mathrm{ord}_v(a) = -\log \mathrm{v}(a_{\mathrm{fin}}(v))$, of the following quantity: the tilt factor $\prod_{i} \bigl(\sqrt{N_{v_i}}\, s_{v_i}\bigr)^{-n(i)}$, times $c'$, times $\sum_{\xi \in \Xi}$ of the integral over $z_S$ of $\xi(z_S)$ multiplied by the sum of two window terms, the integral being taken with respect to the pushforward under [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90) (which keeps the archimedean part and truncates the finite part outside $S_K$) of the restriction of $\nu_{Z_K}$ to the subgroup of unit ideles whose finite components outside $S_K$ lie, together with those of the inverse, in the local integers.
--
--   The first window term is
--   $$\Bigl(\prod_w \|u_w - 1\|^{\,w.\mathrm{mult}}\Bigr) \Bigl(\prod_w \bigl(\|1 - (u^{-1})_w\| \big/ \sqrt{\|(u^{-1})_w\|}\bigr)^{\,w.\mathrm{mult}}\Bigr)^{-1} \cdot \Bigl[ B_d + \sum_{w \text{ real}} \|1 - (u^{-1})_w\|\, C_{d,w} + \sum_{w \text{ complex}} \|1-(u^{-1})_w\|^2 \log\|1-(u^{-1})_w\|\, E_{d,w} \Bigr] \cdot \prod_{v \in S_K} \Phi_{f,v}\bigl(u_v, (z_S)_v\bigr),$$
--   where $u_w$ denotes the $w$-component of the archimedean part of the principal idele of $u$ (obtained through `adeleArch` and `archEval`), each of $B_d$, $C_{d,w}$, $E_{d,w}$ is evaluated at the pair consisting of the mixed-space image of the archimedean part of the principal idele of $u^{-1}$ and of the mixed-space image of the archimedean part of $z_S \cdot u$, and $u_v$, $(z_S)_v$ denote the $v$-components of the finite parts.
--
--   The second window term is $\Phi_a$ evaluated at the pair of mixed-space images of the archimedean parts of the principal idele of $u$ and of $z_S$, times
--   $$\sum_{v \in S_K} \|u_v - 1\| \cdot \bigl(\mathtt{ratio}\,(\|\cdot\|)\,(a_v, b_v)\cdot \mathtt{sqrtRatio}\,(\|\cdot\|)\,(a_v,b_v)\bigr)^{-1}\, \Psi_{f,v}\bigl(a_v, (u_v)^{-1}\bigr) \prod_{v' \in S_K \setminus \{v\}} \Phi_{f,v'}\bigl(u_{v'}, (z_S)_{v'}\bigr),$$
--   where $a_v$ is the image of $z_S \cdot u$ in $K_v^{\times}$ under the place map [`AutomorphicForm.adelePlaceAlgHom`](def/AutomorphicForm_BaseChangePlaces.html#L20), $b_v = a_v \cdot (u_v)^{-1}$ with $u_v$ the corresponding image of the principal idele of $u$, and by definition $\mathtt{ratio}\,(\mathrm{nrm})(a,b) = \mathrm{nrm}(1 - b a^{-1})$ and $\mathtt{sqrtRatio}\,(\mathrm{nrm})(a,b) = \sqrt{\mathrm{nrm}(a)/\mathrm{nrm}(b)}$, taken here for $\mathrm{nrm} = \|\cdot\|$ on $K_v$.
--
--   On the right-hand side stands
--   $$\sum_{i=0}^{\infty} \mathrm{lam}(i) \sum_{\gamma \in \mathrm{sub}(i)} \bigl[\gamma_2 + n_0(i) = n\bigr]\Bigl( B_w(\mathrm{shape}(i))(P_{i,\gamma}) + \sum_{k \in \mathrm{Fin}\,q} \bigl|1 - e^{(x_0(i)+\gamma_1)(kR(k))}\bigr|\, C_w(\mathrm{shape}(i),k)(P_{i,\gamma}) + \sum_{j} \|1 - e^{z_{i,\gamma,j}}\|^2 \log\|1 - e^{z_{i,\gamma,j}}\|\, E_w(\mathrm{shape}(i),j)(P_{i,\gamma}) \Bigr),$$
--   where $P_{i,\gamma} = (x_0(i) + \gamma_1,\; \theta_0(i) + \mathrm{lift}(\gamma))$, the index $j$ runs over $\mathrm{Fin}(r+\#T)$, $z_{i,\gamma,j} = (x_0(i)+\gamma_1)(kC(j))/2 + 2\pi \mathrm{i}\,(\theta_0(i)+\mathrm{lift}(\gamma))(j)$, and the bracket denotes the indicator of the condition $\gamma_2 + n_0(i) = n$ (the summand being $0$ otherwise); both sums are unconditional sums (`tsum`), the inner one over the subgroup $\mathrm{sub}(i)$.
--
--   This is the class-sum identity for the discrepancy (kink) window family attached to a single number field $K$: the tilted sums over the $(S_K \cup T)$-units of a character-folded discrepancy window, with prescribed $T$-valuation vector $n$, are expressed as an absolutely summable family of twisted lattice sums of finitely many smooth periodic kink shapes. It is used in the comparison of hyperbolic terms of trace formulae, being cited by [`AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
    (K : Type) [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v)
    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ f v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ f v = ζ v)

    (Φa : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hΦa_smooth : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦa_cs : HasCompactSupport Φa)
    (hΦa_units : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)))
    (Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCa : IsCompact Ca)
    (hΦa_Ca : ∀ p ∈ tsupport Φa, ∃ q ∈ Ca,
      p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])

    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ SK, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)

    (Bd : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (Cd Ed : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hBd_smooth : ContDiff ℝ (⊤ : ℕ∞) Bd) (hCd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cd w))
    (hEd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ed w))
    (hBd_cs : HasCompactSupport Bd) (hCd_cs : ∀ w, HasCompactSupport (Cd w)) (hEd_cs : ∀ w, HasCompactSupport (Ed w))
    (hBCE_units : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, (Bd p ≠ 0 ∨ ∃ w, Cd w p ≠ 0 ∨ Ed w p ≠ 0) →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)))
    (CaD : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCaD : IsCompact CaD)
    (hBCE_Ca : ∀ p ∈ tsupport Bd ∪ ⋃ w, (tsupport (Cd w) ∪ tsupport (Ed w)),
      ∃ q ∈ CaD, p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)])

    (Ψf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
    (hΨf_cs : ∀ v ∈ SK, HasCompactSupport (Ψf v))
    (hΨf_lc : ∀ v ∈ SK, ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψf v q = Ψf v p)
    (hΨf_cells : ∀ v ∈ SK, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤
            ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
          Ψf v (a', t') = Ψf v (a, t))
    (hΨf_germ : ∀ v ∈ SK, ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψf v (a, t) - Ψf v (a, 1)‖ ≤ C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
        (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|))

    (C c' : ℂ) :
    ∃ (A q : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (kC : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → Fin (Fintype.card (NumberField.InfinitePlace K))) (kR : Fin q → Fin (Fintype.card (NumberField.InfinitePlace K)))
        (Bw : Fin A → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Cw : Fin A → Fin q → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Ew : Fin A → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ),
        (∀ a, ContDiff ℝ (⊤ : ℕ∞) (Bw a)) ∧ (∀ a k, ContDiff ℝ (⊤ : ℕ∞) (Cw a k)) ∧ (∀ a j, ContDiff ℝ (⊤ : ℕ∞) (Ew a j)) ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          Bw a (p.1, p.2 + Pi.single j 1) = Bw a p ∧ (∀ k, Cw a k (p.1, p.2 + Pi.single j 1) = Cw a k p) ∧
            ∀ j', Ew a j' (p.1, p.2 + Pi.single j 1) = Ew a j' p) ∧
      ∃ (Sx : Set (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)), IsCompact Sx ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), p.1 ∉ Sx → Bw a p = 0 ∧ (∀ k, Cw a k p = 0) ∧ ∀ j, Ew a j p = 0) ∧
      ∃ (sub : ℕ → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (shape : ℕ → Fin A) (lam : ℕ → ℂ), (Summable fun i => ‖lam i‖) ∧
      ∃ (x₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : ℕ → Fin T.card → ℤ) (θ₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        C *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (f (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (c' * ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                      (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) +
              Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] *
                ∑ v ∈ SK, (((‖((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ) * ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) *
                        AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) : ℝ)) : ℂ))⁻¹ * Ψf v ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹))) *
                  ∏ v' ∈ SK.erase v, Φf v' (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v',
                      (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        ∑' i : ℕ, lam i * ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            Bw (shape i) (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kR k))| : ℝ) : ℂ) * Cw (shape i) k (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card), ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                    Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
                Ew (shape i) j (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by sorry
