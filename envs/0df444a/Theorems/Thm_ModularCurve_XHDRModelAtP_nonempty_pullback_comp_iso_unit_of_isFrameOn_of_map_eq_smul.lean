-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul
-- name    : ModularCurve.XHDRModelAtP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/c1d7569d-cbe7-5d5f-ac1d-8bf976affb21
-- title:
--   Triviality of the glued module on both special-fibre components
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; assume $j(q) \in$ the $q$-expansion function field over $\mathbb{Q}$ at full level, let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` and assume `toBase p (ΓM M H) hj` proper. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p \in A$ a nonunit, whose residue field is algebraically closed of characteristic $p$, and $\rho : R_p \to A$ a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Write $X$ for the base change $\mathrm{pullback}(\mathrm{toBase}\,p\,(\Gamma_M)\,hj, \mathrm{Spec}\,\rho)$ and let $bc$ be a morphism from the fibre of the level-$\Gamma_M$ model along $A \to A/\mathfrak{m}_A$ composed with $\rho$ into $X$, compatible with the first projection and with the second projection up to $\mathrm{Spec}$ of the residue map. Let $e \ge 1$, let $U \subseteq X$ be open, and let $f : U \to \mathrm{Spec}\,Q$, $Q = A[u,v]/(uv - p^e)$, be a morphism over $\mathrm{Spec}\,A$ (i.e. $f$ followed by $\mathrm{Spec}(A \to Q)$ equals the inclusion $U \hookrightarrow X$ followed by the second projection), oriented in the sense that points of $U$ lying in the image of $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0$ followed by $bc$ have $v$ in their prime, and those in the image of the index-$1$ morphism have $u$ in their prime. Let $x', y' \in \mathfrak{m}_A$ with $x'y' = p^e$ and $w \in A^\times$; on $\mathrm{Spec}\,Q$ put $a = u - x'$, $b = y' - v$, $a_w = u - wx'$, $b_w = y' - wv$ (as global sections via the canonical identification of $Q$ with $\Gamma(\mathrm{Spec}\,Q,\top)$) and $O = (D(a) \cup D(b)) \cap (D(a_w) \cup D(b_w))$. The assertion is: for every section $g$ of $\mathcal{O}$ over $D(a) \cup D(b)$ with $g\,a = a_w$ on $D(a)$ and $g\,b = b_w$ on $D(b)$; for all opens $W_2, W_3 \subseteq X$ with $W_2 \cup W_3 = X$, $W_2 \le U$ and $W_2 \cap W_3 \le U.\iota(f^{-1}O)$, putting $t \in \Gamma(X, W_2 \cap W_3)$ for the restriction of the pullback along $f$ of $g|_O$ (transported along the open immersion $U \hookrightarrow X$); and for every $\mathcal{O}_X$-module $L$ with sections $a_L$ over $W_2$ and $b_L$ over $W_3$ that are frames in the sense of `IsFrameOn` (multiplication by the restriction of the section is a bijection $\Gamma(X,W) \to \Gamma(L,W)$ for every open $W$ contained in the given opens) and satisfying $b_L|_{W_2 \cap W_3} = t \cdot a_L|_{W_2 \cap W_3}$ — for each $i \in \{0,1\}$ the pullback of $L$ along $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i$ followed by $bc$ is isomorphic to the unit object of the category of modules on the fibre of the level-$\Gamma_N$ model along $A \to A/\mathfrak{m}_A$ composed with $\rho$.
--
--   This is the crossing-chart case of the triviality step in the analysis of the inertia action on the special fibre of the model of $X_H$ at $p$: a module glued from frames on a two-piece cover by a transition function coming from a displacement unit $(u - wx')/(u - x')$ on a node chart becomes trivial when restricted to either of the two components of the special fibre, since the pulled-back transition function becomes a unit constant there. It feeds the construction of the invertible module attached to a point in [`ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter), via the general gluing criterion [`AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul`](thm.html#AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul) and the stability of frames under pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel MvPolynomial
open scoped MatrixGroups

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bc).base →
      CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bc).base →
      CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal)

    (x' y' : ↥A) (hxy : x' * y' = ((p : ℕ) : ↥A) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥A) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥A) (w : (↥A)ˣ) :
    letI X : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q ((w : ↥A) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - algebraMap ↥A Q (w : ↥A) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      ∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ bc)).obj L ≅
        𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules) := by sorry
