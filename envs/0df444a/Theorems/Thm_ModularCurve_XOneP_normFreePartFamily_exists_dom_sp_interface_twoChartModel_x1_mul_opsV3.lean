-- Prove2me | Theorems.Thm_ModularCurve_XOneP_normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3
-- name    : ModularCurve.XOneP.normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/8e6f6589-370a-54db-a0a2-62371cf47da3
-- title:
--   Specialisation datum for the norm-free part of J₁(Mp)
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $5 \le M$ and $p \nmid M$; $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. The field $K$ is an intermediate field of $L \subseteq L((q))$, required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of the Laurent series field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. The ring $A$ is a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal (`hAp`) and $\zeta$ in the image of $A$ (`hζA`), and $K$ is an $A$-algebra compatibly with $L$. The element $j \in K$ is nonzero and has, by `hj`, the $q$-expansion $\mathrm{coeffEmb}_L(\mathtt{jq})$ of the modular invariant. The scheme $X := \mathrm{TwoChartModel}(A,K,j)$, the pushout of the two affine charts $\mathrm{Spec}$ of the $A$-subalgebras of $K$ of elements integral over $A[j]$ and over $A[j^{-1}]$, comes with its structure morphism $\pi :=$ [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) to $\mathrm{Spec}\,A$, assumed proper. Finally `Pl` is a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$ and is an $A$-algebra, and $\overline{\mathbb{Q}}$ is an $A$- and $L$-algebra compatibly.
--
--   The hypotheses fall into the following groups; each group is named, and the content of the larger ones is summarised.
--
--   *Special fibre geometry.* Two schemes $C_1,C_2$ with morphisms $c_1,c_2$ to $\mathrm{Spec}\,\kappa$, each proper, smooth of relative dimension $1$ and geometrically integral, together with closed immersions $i_1,i_2$ of $C_1,C_2$ into the base change $X_\kappa$ of $\pi$ along $A \to \kappa$, over $\mathrm{Spec}\,\kappa$; `hcover` says that every point of $X_\kappa$ lies in the image of $i_1$ or of $i_2$; `hred` says that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` say that its number of points is $n > 0$.
--
--   *Sections.* A section $\varepsilon$ of $\pi$ over $\mathrm{Spec}\,A$, sections $\varepsilon_1,\varepsilon_2$ of $c_1,c_2$, and `hε₁`: $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $\kappa$.
--
--   *Relative Picard data.* A designation $D$ (a scheme $D.P$ over $\mathrm{Spec}\,A$ with a zero section) together with `hrep`, the nonemptiness of the datum `RepresentsRelSubPic` for $\pi$, $\varepsilon$ and the cut `algEquivZeroCut` of fibrewise algebraically trivial rigidified line bundles: a Poincaré rigidified bundle on $D.P$ whose pullbacks classify such bundles uniquely, and which is trivial along the zero section. Further: `hsm`, `hsep` ($D$'s structure morphism is smooth and separated); `hreps`, the same representability over $\kappa$ for $D \otimes \kappa$ and the base-changed section; `hPk`, an isomorphism of the Poincaré bundle of `hreps` with the base change of the one of `hrep`; designations $D_1,D_2$ with representability data `hrep₁`, `hrep₂` for $c_1,\varepsilon_1$ and $c_2,\varepsilon_2$; and a morphism $\nu_2$ from $(D\otimes\kappa)$'s base to $D_2$'s base such that (`hν₂`) for every $\kappa$-scheme $t : T \to \mathrm{Spec}\,\kappa$ and every $T$-point $a$ of $(D\otimes\kappa)$, the pullback of the Poincaré bundle of `hrep₂` along $a$ followed by $\nu_2$ is isomorphic to the rigidification along `rigSection c₂ t ε₂` of the restriction along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   *Base change to $L$ and to $\overline{\mathbb{Q}}$.* `hsmL`, `hgiL`: $X_L$ is smooth of relative dimension $1$ and geometrically integral over $L$; `hprL`, `hgcL`: $D \otimes L$ is proper and geometrically connected over $L$. A curve model $M\eta$ over $\overline{\mathbb{Q}}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182), an isomorphism $e\eta$ of $M\eta.C$ with $X_{\overline{\mathbb{Q}}}$ compatible with the structure morphisms (`heη`), the nonemptiness of the preimage in $M\eta.C$ of the finite chart, and two pinning hypotheses: `hMηpin` says that for every element $a$ of the finite chart algebra the corresponding element of the function field of $M\eta$ has as $q$-expansion the coefficientwise image in $\overline{\mathbb{Q}}((q))$ of the $q$-expansion of $a$ in $L((q))$; `hgal` says that for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing $L$ pointwise and for $\overline{\mathbb{Q}}$-points $x,x'$ of $M\eta.C$, if $x'$ read in the finite chart is the $g$-twist of $x$ so read, then the place attached to $x'$ is the image of the place attached to $x$ under [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) applied to $g$.
--
--   *Hecke inputs and the Galois action on $A$.* `hin : ModularCurve.HeckeDiamondInputsAll (M * p)` and `hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p)`; a multiplicative semiring action of $\mathrm{Gal}(L/\mathbb{Q})$ on $A$ with `hΓA` asserting compatibility with $A \to L$.
--
--   *Abstract special fibre.* A datum $G$ consisting of abelian groups $G.J0s$, $G.JI$, $G.JE$, a subgroup $G.\mathrm{torus}$ and a surjection $G.\mathrm{proj}$ onto $G.JI \times G.JE$ with kernel $G.\mathrm{torus}$; bijections `pts`, `ptsI`, `ptsE` of these groups with the $\kappa$-points of $D\otimes\kappa$, $D_1$, $D_2$; hypotheses `hadd`, `haddI`, `haddE` that addition corresponds to tensor product of the pulled-back Poincaré bundles; `hPTS` that `pts` is additive and sends $0$ to the unit point; and `hproj`, stating that for $x \in G.J0s$ the first component of $G.\mathrm{proj}\,x$ corresponds under `ptsI` to `pts x` postcomposed with the restriction morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and the second component to `pts x` postcomposed with $\nu_2$.
--
--   *Global points, Hecke and Galois operators.* A bijection `gpts` of $J_1(Mp) :=$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) with the $\overline{\mathbb{Q}}$-points of $D$ over $A$; a map $\varphi$ from the Hecke algebra [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) (the polynomial ring on generators indexed by primes and by natural numbers) to endomorphisms of $D$ over $\mathrm{Spec}\,A$; for each $s \in \mathrm{Gal}(L/\mathbb{Q})$ a semilinear endomorphism $\tau(s)$ of $D$ over the $s$-twist of the base. These satisfy: `hφmul` (each $\varphi(t)$ is additive for the relative group law of `hrep`), `hφpts` (postcomposition with $\varphi(t)$ matches the Hecke action on $J_1(Mp)$ through `gpts`), `hτ1`, `hτmul` ($\tau(1)$ is the identity and $\tau(ss')$ is $\tau(s)$ followed by $\tau(s')$), `hτφ` ($\tau$ and $\varphi$ commute), `hgadd` (`gpts` is additive for the relative group law) and `hτpts` (for $\sigma'$ on $\overline{\mathbb{Q}}$ restricting to $s$ on $L$, the point of $\sigma' \cdot x$ is $\mathrm{Spec}(\sigma')$ followed by the point of $x$ followed by $\tau(s^{-1})$).
--
--   *Abel–Jacobi data over $L$ and $\overline{\mathbb{Q}}$.* Representability `hDL` over $L$, a morphism `ajL` from $X_L$ to $D \otimes L$ over $L$, the comparison morphism `kL` from $X_{\overline{\mathbb{Q}}}$ to $X_L$ with `hkL₁`, `hkL₂`, the base-change isomorphism `hPL` of Poincaré bundles, `hajLε` (`ajL` sends the base-changed cusp section to the zero section), and `hajL`: for every field $K'$, every $K'$-point $x$ of $X_L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of the cusp section, i.e. `ajL` classifies $[x] - [\varepsilon]$. Further, a morphism `ajbar` from $M\eta.C$ to $D.P$ given by `hajbar` as $e\eta$ followed by `kL`, `ajL` and the first projection, lying over the base by `hajbar_over`; a $\overline{\mathbb{Q}}$-point `εbar` of $M\eta.C$ with `hεbar` (it is the cusp) and `hεbar_aj` (`ajbar` carries it to the zero section); and `hpts_aj`: for $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M\eta.C$ with $s$ the cusp, there is a degree-zero divisor $Dv = [x] - [s]$ on the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) whose class has `gpts`-point equal to $x$ followed by `ajbar`.
--
--   *Special fibre operators.* A datum $O$ of operators on $G$ (Hecke operators on $G.J0s$, $G.JI$, $G.JE$ compatible with $G.\mathrm{proj}$ away from $p$, diamond operators `diamondP`, `diamondN`, an involution, an inertia action, a Verschiebung on $G.JI$, a Frobenius on $G.JE$, with the listed commutation relations), and `hO`, four clauses matching these on $\kappa$-points with the global operators: `O.hecke ℓ` with $\varphi(\mathtt{heckeGenOne}\,\ell)$ for every prime $\ell$; `O.diamondP b` with $\varphi(\mathtt{diamondGen}\,d)$ for every $d$ coprime to $Mp$ with $d \equiv 1 \bmod M$ and $d \equiv b \bmod p$; `O.diamondN d` with $\varphi(\mathtt{diamondGen}\,d)$ for every $d$ coprime to $Mp$ with $d \equiv 1 \bmod p$; and `O.inertia b` with $\tau(s)$ for every $s \in \mathrm{Gal}(L/\mathbb{Q})$ with $s\zeta = \zeta^{b}$.
--
--   *The place and its rings.* `hPl`: $p$ lies in the nonunits of `Pl`; a ring map $\rho : A \to$ `Pl` with `hρ` recovering $A \to \overline{\mathbb{Q}}$, and `hAlgκ` identifying $A \to \kappa$ with the residue map composed with $\rho$.
--
--   *The $\mathcal{O}_I$-points hypothesis `hF3` (five clauses, summarised here).* For every subgroup $I$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup at `Pl`, fixing every $p$-th root of unity, and of finite index in that inertia subgroup, writing $\mathcal{O}_I$ for the intersection of `Pl` with the fixed field of $I$, there exist a ring map $\rho_I : A \to \mathcal{O}_I$ lifting $A \to \overline{\mathbb{Q}}$ such that, with $\mathrm{dom}$ the set of $x \in J_1(Mp)$ whose $\overline{\mathbb{Q}}$-point factors through an $\mathcal{O}_I$-point of $D$ over $\rho_I$: every element of $\mathrm{dom}$ is fixed by $I$; distinct $\mathcal{O}_I$-points of $D$ have distinct $\overline{\mathbb{Q}}$-points; $\mathrm{dom}$ contains $0$ and is closed under subtraction; for each $n > 0$ prime to $p$, reduction to $\kappa$ is injective on the $n$-torsion of the group of $\mathcal{O}_I$-points and hits every $n$-torsion $\kappa$-point; and $\mathrm{dom}$ is stable under any Frobenius at `Pl` for $p$ that normalises $I$.
--
--   *The subgroup scheme $\mathcal{A}$ and the diamond norm.* A scheme $\mathcal{A}$ with structure morphism $a$ to $\mathrm{Spec}\,A$ and a morphism $\iota$ to $D$ over $a$, subject to `h𝒜` (six clauses, summarised here): $\iota$ is a closed immersion; $a$ is proper and smooth; all geometric fibres of $a$ are connected; the points of $\mathcal{A}$ form a subgroup of the points of $D$ for the relative group law of `hrep`, functorially in the base; the $\overline{\mathbb{Q}}$-points of $\mathcal{A}$ are exactly the points `gpts x` for $x$ in the subgroup [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) of $J_1(Mp)$, the image of the endomorphism `normFreeEnd` attached to the norm-free representatives at $p$; and $\mathcal{A}$ is stable under every $\varphi(t)$. The hypothesis `hF10` states that for every commutative $\kappa$-algebra $T'$ and every $T'$-point $v$ of $D \otimes \kappa$ which factors through $\mathcal{A}$, composing $v$ (read in $D.P$) with $\varphi$ of $\sum_{b \in (\mathbb{Z}/p)^{\times}} \mathtt{diamondGen}\,d_b$, where $d_b$ is the natural number supplied by the Chinese remainder isomorphism from $(b,1) \in \mathbb{Z}/p \times \mathbb{Z}/M$, gives the unit point over the corresponding base morphism.
--
--   *Igusa components.* An integral weight one form $w$ on $\Gamma_1(M)$ over $\kappa$ (a weight one modular form together with an integral power series realising its $q$-expansion, whose reduction over $\kappa$ is nonzero), two curve models $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ over $\kappa$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) — the field obtained from the $q$-expansion function field of $X_1(M)$ over $\kappa$ by adjoining the inverse of the reduced series of $w$ — with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`), the nonemptiness of the relevant chart preimage in $\mathrm{Mdl}_1.C$, and the $q$-expansion pinning `hgauss₁`: for $a$ in the finite chart algebra and power series $x,y$ over $A$ with $y$ having nonzero reduction, if $a \cdot y = x$ in $L((q))$ then the function field element of $\mathrm{Mdl}_1$ read off from $a$ along $e_1$ and $i_1$ has $q$-expansion the reduction of $x$ divided by that of $y$. In addition `hεC₂` says that the reduction of the cusp section misses $C_2$, and `hεgal` is a Galois equivariance of the cusp section: for $s \in \mathrm{Gal}(L/\mathbb{Q})$, any endomorphism $w_s$ of the two-chart model over the $s$-twist of $\mathrm{Spec}\,A$ which is induced on the finite chart by a ring automorphism acting on $q$-expansions coefficientwise by $s$ satisfies $\varepsilon$ followed by $w_s$ equals the $s$-twist followed by $\varepsilon$.
--
--   *Raynaud-type identification `hF4c` (seven clauses, summarised here).* A finite set `nodesIg` of pairs of places of the Igusa function field, additive isomorphisms $\Psi$ of $G.J0s$ with [`AlgebraicCurve.GluedPic0 κ`](def/AlgebraicCurve_GluedPic0.html#L201) of the Igusa field along `nodesIg` (the admissible gluing data — pairs of degree-zero divisors vanishing at the glued places together with units at the nodes — modulo glued principal data), and $\theta_1,\theta_2$ of $G.JI$, $G.JE$ with $\mathrm{Pic}^0$ of the Igusa function field. The clauses require: `nodesIg` consists exactly of the pairs of places coming from $\kappa$-points of the intersection `pullback i₁.1 i₂.1`, read through $e_1^{-1}$, $e_2^{-1}$ and the point-place bijections of $\mathrm{Mdl}_1$, $\mathrm{Mdl}_2$; its cardinality is $n$; both projections are injective on it; the pair map `GluedPic0.toPic0Pair` composed with $\Psi$ equals $(\theta_1,\theta_2)$ composed with $G.\mathrm{proj}$; $\Psi$ carries $G.\mathrm{torus}$ onto the range of `GluedPic0.nodeUnit`; and $\theta_1$, $\theta_2$ compute Abel–Jacobi classes, in the sense that if the pullback of the Poincaré bundle along `ptsI g` (resp. `ptsE g`) is isomorphic to the line bundle of a $\kappa$-point $x$ tensored with the ideal module of $\varepsilon_1$ (resp. $\varepsilon_2$), then $\theta_1 g$ (resp. $\theta_2 g$) is the class of $[x] - [\varepsilon_1]$ (resp. $[x] - [\varepsilon_2]$). Finally a semilinear automorphism `frobT` of the Igusa function field over $\kappa$ which, by `hfrobT`, raises every $q$-expansion coefficient to the $p$-th power.
--
--   Under all of these hypotheses the assertion is the following. Let $I$ be any subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup at `Pl`, fixing every $p$-th root of unity in $\overline{\mathbb{Q}}$, and of finite index in that inertia subgroup. Then there exist an additive subgroup $\mathrm{dom}$ of $J_1(Mp)$ and an additive homomorphism $\mathrm{sp}$ from $\mathrm{dom}$ to `GluedPic0` of the Igusa function field along `nodesIg` with the following five properties.
--
--   First, the interface, in two clauses: an element $y$ of $J_1(Mp)$ lies in $\mathrm{dom}$ if and only if its $\overline{\mathbb{Q}}$-point `(gpts y).1` factors as $\mathrm{Spec}$ of the inclusion of $\mathcal{O}_I =$ `Pl` $\cap\ \overline{\mathbb{Q}}^{\,I}$ into $\overline{\mathbb{Q}}$ followed by a morphism $z$ from $\mathrm{Spec}\,\mathcal{O}_I$ to $D.P$ lying over $\mathrm{Spec}$ of the ring map chosen from `hF3 I hI hIμ hIf`; and, for $y \in \mathrm{dom}$, for any such $z$ realising the factorisation and any $\kappa$-point $u$ of $D \otimes \kappa$ whose associated morphism to $D.P$ equals $\mathrm{Spec}$ of the residue map of `Pl` composed with the inclusion $\mathcal{O}_I \subseteq$ `Pl`, followed by $z$, one has $\mathrm{sp}(y) = \Psi(\mathtt{pts}^{-1}(u))$.
--
--   Secondly, every $y \in \mathrm{dom}$ is fixed by every $\sigma \in I$.
--
--   Thirdly, for every automorphism $\phi$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius at `Pl` for $p$ and satisfies $\sigma \in I \iff \phi\sigma\phi^{-1} \in I$ for all $\sigma$, and every $y \in \mathrm{dom}$, the element $\phi \cdot y$ again lies in $\mathrm{dom}$.
--
--   Fourthly, $\mathrm{sp}$ is injective on torsion of order prime to $p$: if $y \in \mathrm{dom}$ is killed by some $n > 0$ with $p \nmid n$ and $\mathrm{sp}(y) = 0$, then $y = 0$.
--
--   Fifthly, $\mathrm{sp}$ hits all such torsion: for every $\xi$ in `GluedPic0` killed by some $n > 0$ with $p \nmid n$, there is $y \in \mathrm{dom}$, itself killed by some $n > 0$ with $p \nmid n$, with $\mathrm{sp}(y) = \xi$.
--
--   This is the per-subgroup existence step for the specialisation of $J_1(Mp)$ at a place above $p$: over the assembled semistable model of $X_1(Mp)$ and Raynaud's description of the special fibre Picard group as a glued Picard group of the two Igusa components, it produces, for each finite-index subgroup $I$ of inertia fixing $\mu_p$, the domain of definition of the specialisation map together with the map itself, its Galois and Frobenius equivariance, and the bijectivity on torsion of order prime to $p$. It is used by [`ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div), which assembles these data into the pinned specialisation family for the norm-free part of $J_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV3
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinned
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinnedV3
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open ModularCurve IntermediateField

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in

theorem ModularCurve.XOneP.normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)] [CharP (IsLocalRing.ResidueField ↥Pl) p] [Algebra A (IsLocalRing.ResidueField ↥Pl)]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (c₂ : C₂ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl))) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)) (D.baseChange (IsLocalRing.ResidueField ↥Pl)))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε (IsLocalRing.ResidueField ↥Pl)
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (a : SchemeHomOver t (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (O : ModularCurve.JOneP.NeronSpecialFibreOpsV3 G)
    (hO :
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (y : G.J0s),
        (pts (O.hecke ℓ y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).1) ∧
      (∀ (b : (ZMod p)ˣ) (d : ℕ), d.Coprime (M * p) → (d : ZMod M) = 1 → (d : ZMod p) = (b : ZMod p) →
        ∀ y : G.J0s,
          (pts (O.diamondP b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
            ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧
      (∀ d : ℕ, d.Coprime (M * p) → (d : ZMod p) = 1 → ∀ y : G.J0s,
        (pts (O.diamondN d y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧

      (∀ (b : (ZMod p)ˣ) (s : L ≃ₐ[ℚ] L), s ζ = ζ ^ (b : ZMod p).val → ∀ y : G.J0s,
        (pts (O.inertia b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (τ s).1) )
    (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (hAlgκ : algebraMap A (IsLocalRing.ResidueField ↥Pl) = (IsLocalRing.residue ↥Pl).comp ρ)
    (hF3 : ∀
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
    (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
    (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),

    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    ∃ (ρI : A →+* ↥OI) (hρI : OI.subtype.comp ρI = algebraMap A (AlgebraicClosure ℚ)),

      let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)

      let DOI := SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase
      let Dκ := SchemeHomOver (Spec.map (CommRingCat.ofHom (toκ.comp ρI))) D.toBase

      let dom : Set (ModularCurve.JOne (M * p)) :=
        {x | ∃ z : DOI, (gpts x).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1}

      (∀ x ∈ dom, ∀ σ ∈ I, σ • x = x) ∧

      (∀ z z' : DOI, Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z'.1 → z = z') ∧

      (0 ∈ dom ∧ ∀ x ∈ dom, ∀ y ∈ dom, x - y ∈ dom) ∧

      (letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom ρI))
       letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom (toκ.comp ρI)))
       ∀ n : ℕ, 0 < n → ¬ p ∣ n →
         (∀ z : DOI, z ^ n = 1 → Spec.map (CommRingCat.ofHom toκ) ≫ z.1 = (1 : Dκ).1 → z = 1) ∧
         (∀ w : Dκ, w ^ n = 1 → ∃ z : DOI, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom toκ) ≫ z.1)) ∧

      (∀ φ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Pl.IsFrobeniusAt φ' p →
        (∀ σ, σ ∈ I ↔ φ' * σ * φ'⁻¹ ∈ I) → ∀ x ∈ dom, φ' • x ∈ dom))
    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)
    (h𝒜 :

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)))
    (hF10 :
    ∀ (T' : Type) [CommRing T'] [Algebra (IsLocalRing.ResidueField ↥Pl) T']
      (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T'))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
      (∃ z : Spec (CommRingCat.of T') ⟶ 𝒜,
          z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl) ∧
          v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = z ≫ ι.1) →
      (v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫
          (φ (∑ b : (ZMod p)ˣ, ModularCurve.diamondGen
            ((ZMod.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpM)).symm ((b : ZMod p), 1)).val)).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl))).1)

    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField ↥Pl) M)
    (Mdl₁ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl)) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (x.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))) / HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))))

    (hεC₂ : ∀ t, ((sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1).base t ∉ Set.range i₂.1.base)
    (hεgal : ∀ (s : L ≃ₐ[ℚ] L) (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j),
      ws ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) →
      ∀ (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) →
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)
    (hPTS :
    (∀ a b : G.J0s, pts (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _ (pts a) (pts b)) ∧
    pts 0 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).one _)
    (nodesIg : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)))
    (Ψ : G.J0s ≃+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg)
    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (θ₂ : G.JE ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hF4c :

      (∀ σ : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w),
        σ ∈ nodesIg ↔ ∃ (z : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ pullback i₁.1 i₂.1)
          (hz₁ : (z ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : (z ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _),
          σ.1 = Mdl₁.pointEquivPlace ⟨(z ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact hz₁⟩ ∧
          σ.2 = Mdl₂.pointEquivPlace ⟨(z ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact hz₂⟩) ∧
      nodesIg.card = n ∧
      Set.InjOn Prod.fst (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧
      Set.InjOn Prod.snd (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧

      (∀ x : G.J0s, AlgebraicCurve.GluedPic0.toPic0Pair nodesIg (Ψ x) = (θ₁ (G.proj x).1, θ₂ (G.proj x).2)) ∧

      (G.torus.map Ψ.toAddMonoidHom = (AlgebraicCurve.GluedPic0.nodeUnit nodesIg).range) ∧

      (∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁),
        Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
          (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
          θ₁ g = Pic0.mk Dv) ∧

      (∀ (g : G.JE) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE g)).L ≅
          (RelEffCartierDiv.ofPoint c₂ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₂.pointEquivPlace ⟨x.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 ∧
          θ₂ g = Pic0.mk Dv))
    (frobT : SemilinearAut (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hfrobT : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (n : ℤ),
      ((frobT • x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n = ((x : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n) ^ p)
    :
    ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
    ∃ (dom : AddSubgroup (ModularCurve.JOne (M * p)))
      (sp : ↥dom →+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg),
      ((∀ y : ModularCurve.JOne (M * p), y ∈ dom ↔ ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) ∧
      (∀ (y : ModularCurve.JOne (M * p)) (hy : y ∈ dom) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase)
        (hz : (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
        u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1 →
        sp ⟨y, hy⟩ = Ψ (pts.symm u))) ∧

      (∀ y ∈ dom, ∀ σ ∈ I, σ • y = y) ∧

      (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          Pl.IsFrobeniusAt φ p → (∀ σ, σ ∈ I ↔ φ * σ * φ⁻¹ ∈ I) → ∀ y ∈ dom, φ • y ∈ dom) ∧

      (∀ y : dom,
          (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧
            n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))) = 0) →
            sp y = 0 → y = 0) ∧

      (∀ ξ : GluedPic0 (IsLocalRing.ResidueField ↥Pl) (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • ξ = 0) →
          ∃ y : dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧
            n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))) = 0) ∧ sp y = ξ) := by sorry
