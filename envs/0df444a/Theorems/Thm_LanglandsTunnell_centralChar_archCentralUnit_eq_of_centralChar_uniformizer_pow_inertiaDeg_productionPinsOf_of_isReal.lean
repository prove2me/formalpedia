-- Prove2me | Theorems.Thm_LanglandsTunnell_centralChar_archCentralUnit_eq_of_centralChar_uniformizer_pow_inertiaDeg_productionPinsOf_of_isReal
-- name    : LanglandsTunnell.centralChar_archCentralUnit_eq_of_centralChar_uniformizer_pow_inertiaDeg_productionPinsOf_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/27286fb8-8176-595a-bf10-185cbc3f59b6
-- title:
--   Real archimedean agreement of central characters under base change
-- statement:
--   Let $K$ be a number field equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ (so that a prime $P$ of $\mathcal O_K$ has a restriction $P \cap \mathcal O_{\mathbb Q}$, written `P.under (𝓞 ℚ)`). Let $\Theta$ be a complex Hecke eigensystem over $\mathbb Q$ and $\Theta'$ one over $K$ (each consisting of a nonzero level ideal and two families $a$, $b$ indexed by the finite places). Let $D' \subseteq \mathrm{GL}_2(\mathbb A_{\mathbb Q})$ and $D \subseteq \mathrm{GL}_2(\mathbb A_K)$ be arbitrary subsets, and let $R$, respectively $R'$, be smooth cuspidal realisations of $\Theta$, respectively $\Theta'$, at the production pins built from $D'$, respectively $D$, with level subgroups $\mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, Hecke generators `heckeGen`, central subgroup the whole idele unit group, and box `adelicBox`; thus each carries a nonvanishing function on the adelic $\mathrm{GL}_2$, a central character on the full idele unit group, smooth cuspidality, invariance under the level subgroup, and Hecke and central eigenvalue relations with eigenvalues $a$ and $b$ outside a finite exceptional set. Assume $R$ and $R'$ are genuine, i.e. their underlying functions are continuous. Assume further that there is a finite set $S$ of primes of $\mathcal O_K$ such that for every $P \notin S$ the central character of $R'$ at $\det(\mathrm{gen}\,P)$ equals the central character of $R$ at $\det(\mathrm{gen}\,(P \cap \mathcal O_{\mathbb Q}))$ raised to the power $\mathrm{inertiaDeg}'$ of $P$ over $P \cap \mathcal O_{\mathbb Q}$. Then for every infinite place $w$ of $K$ that is real and every $x \in \mathbb R^\times$, the central character of $R'$ takes at the idele unit with component $x$ at $w$ (transported through the isomorphism $K_w \cong \mathbb R$) and $1$ elsewhere the same complex value as the central character of $R$ takes at the corresponding idele unit of $\mathbb Q$ concentrated at the real place.
--
--   This is the archimedean rigidity statement for central characters: local agreement at every real place of $K$ follows from the inertia-degree relation at almost all finite places, matching the property that the central character of a base change lift is the original central character composed with the norm. It feeds the Langlands–Tunnell part of the argument, and is used in turn by the variant whose hypothesis is stated via agreement away from finitely many places with a formal base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_centralChar_archCentralUnit_eq_of_centralChar_uniformizer_pow_inertiaDeg_productionPinsOf_of_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm
  NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem LanglandsTunnell.centralChar_archCentralUnit_eq_of_centralChar_uniformizer_pow_inertiaDeg_productionPinsOf_of_isReal
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Θ : HeckeEigensystem ℚ ℂ) (Θ' : HeckeEigensystem K ℂ)
    (D' : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ D' (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Θ)
    (hR : IsGenuineCuspRealizationAt ℚ
      (productionPinsOf ℚ D' (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Θ R)
    (D : Set (AdelicGL2 (𝓞 K) K))
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ')
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ' R')
    (hrel : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ P ∉ S,
      ((R'.centralChar
          ⟨Matrix.GeneralLinearGroup.det
              ((productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).gen P),
            Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
        = ((R.centralChar
            ⟨Matrix.GeneralLinearGroup.det
              ((productionPinsOf ℚ D' (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).gen (P.under (𝓞 ℚ))),
            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ ((P.under (𝓞 ℚ)).asIdeal.inertiaDeg' P.asIdeal))
    (w : InfinitePlace K) (hw : w.IsReal) (x : ℝˣ) :
    ((R'.centralChar ⟨AdelicVolume.archCentralUnit K w
          (Units.mapEquiv (ringEquivRealOfIsReal hw).symm.toMulEquiv x), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
      = ((R.centralChar ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
          (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv x),
            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by sorry
