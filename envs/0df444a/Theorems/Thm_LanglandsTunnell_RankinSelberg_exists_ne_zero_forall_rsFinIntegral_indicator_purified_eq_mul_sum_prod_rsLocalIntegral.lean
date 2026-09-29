-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
-- name    : LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/feaf18da-7baa-55ce-8b48-df0fea5232cf
-- title:
--   Euler factorisation of the cut finite Rankin–Selberg integral
-- statement:
--   Throughout, $\mathbb{A}$ denotes the adele ring of $\mathbb{Q}$, the group $G=GL_2(\mathbb{A})$ is written `AdelicGL2 (𝓞 ℚ) ℚ`, and $G_f=$ `finiteAdelicGL2Subgroup ℚ` is its subgroup of elements with trivial archimedean component (the kernel of `glArch`); [`RSCarrier.finFactor`](def/LanglandsTunnell_RSCarrierSplit.html#L17) sends $g\in G$ to the element of $G_f$ obtained by dividing out its real archimedean factor, and [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) is the upper‑triangular unipotent subgroup `adelicUnipotent ℚ` viewed inside $G_f$. For a finite place $v$ of $\mathbb{Q}$, `localAt ℚ v` is the projection $G\to GL_2(\mathbb{Q}_v)$, [`UnramifiedWhittaker.placeEmbed ℚ v`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) the embedding $GL_2(\mathbb{Q}_v)\to G$, `iotaGL` and `iota` the embeddings $M\mapsto \mathrm{diag}(M,1)$ of $GL_2$ into $GL_3$ locally and adelically, `componentAt3 (𝓞 ℚ) ℚ v` and `archComponent3 (𝓞 ℚ) ℚ` the local and archimedean projections of $GL_3(\mathbb{A})$, and [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15) the module of multiplication by a scalar on $\mathbb{Q}_v$ (zero on $0$), so that $g\mapsto \mathrm{modulus}(\det g)$ is the local determinant absolute value. Finally `detNorm` is the idele norm of the determinant, and for a subgroup $H$ of a group with Haar measure $\mu_H$ the function [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25) is the normalised weight used to turn a measure on the ambient group into one modelling integration over $H\backslash G$.
--
--   Global data and structural hypotheses. A number field $K$ whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$‑algebra is given, together with the hypothesis `_hdeg` that $[K:\mathbb{Q}]=3$, and a finite set $S_Q$ of finite places of $\mathbb{Q}$. The hypothesis `hSQram` requires that every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose prime below lies outside $S_Q$ have ramification index `Ideal.ramificationIdx'` equal to $1$. A homomorphism $\chi_A:\mathbb{A}^\times\to\mathbb{C}^\times$ is given with `hχA` asserting `IsAdmissibleTwist`, i.e. $\chi_A$ is trivial on the principal ideles of $\mathbb{Q}^\times$, continuous and unitary, and with `hχoff` asserting `IsUnramifiedCharAt χA v` for every $v\notin S_Q$, i.e. the local component `localChar χA v` is trivial on those local units $t$ for which both $t$ and $t^{-1}$ are integral. A homomorphism $\nu:\mathbb{A}_K^\times\to\mathbb{C}^\times$ is given with `hνadm` the same admissibility (idele‑class, continuous, unitary) over $K$. An additive character $\psi$ of $\mathbb{A}$ is given with `hψ` the three clauses of `IsGlobalAddChar` (trivial on $\mathbb{Q}$, continuous, nontrivial), with `hψQ` requiring $\psi^{-1}=$ [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), and with `hlev` requiring that the local component `psiLoc ψ v` have `addCharLevel` equal to $0$ at every finite place $v$.
--
--   The $GL_3$ datum. $F$ is a `CubicInductionForm K pins ψ ν` where the carrier `pins` is `productionPinsOf ℚ` applied to the Siegel domain `classRepSiegelSet ℚ (1/2) 1 (1/2) 2` (the union of the translates by class representatives of the centre‑cut Siegel set with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$), the level subgroups $N\mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen (𝓞 ℚ) ℚ v`, and the adelic box `adelicBox ℚ` (whose conditioned additive Haar measure is the measure component of the pins, the group components being the Borel structure `glBorel` and the adelic $GL$ Haar measure, with central subgroup $\top$). Thus $F$ supplies a form `F.form` on $GL_3(\mathbb{A})$, its global, archimedean and local Whittaker functions `F.whittaker`, `F.whittakerArch`, `F.whittakerLoc v`, a central character and a dual Whittaker function, subject to the structure's clauses: automorphy under $GL_3(\mathbb{Q})$, the central‑character law with idele‑class central character, cuspidality along the two maximal parabolics relative to the pins, identification of `whittaker` with `whittaker3 pins ψ form`, the $\psi$‑Whittaker law and the mirabolic expansion, the local $\psi_v$‑Whittaker laws, factorisation of the Whittaker function as the archimedean factor times the local factors over any finite set containing the bad places of $(K,\nu)$, inducedness/sphericality at the good places, invariance of `whittakerLoc v` under `congruenceK1` at places unramified in $K$, local multiplicity one, moderate growth, $K$‑finiteness, and the remaining convergence clauses. The hypothesis `hF0` has two conjuncts: `F.form ≠ 0`, and, for every $v$ not ramified in $K$ with `addCharLevel (psiLoc ψ v) = 0`, both `F.whittakerLoc v 1 = 1` and `HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v)`, the latter prescribing the two families of explicit values of `F.whittakerLoc v` — at the torus points `iotaTorusLocal v n` and at the two‑row points `twoRowPointLocal v k₁ (k₂+1)` with $k_2+1\le k_1$ — in terms of the spherical torus values of the three parameters induced from the coefficients $\mathfrak{P}\mapsto \nu(\varpi_{\mathfrak{P}})$ (set to $0$ at primes where $\nu$ is ramified). The hypothesis `hFw` requires each `F.whittakerLoc v` to be continuous. A distinguished place $p\in S_Q$ is fixed (`hp`).
--
--   The split finite test vector. A function $W_{f0}$ on $G_f$ is given, an integer $m$, slot functions $w_{v,\alpha}$ on $GL_2(\mathbb{Q}_v)$ for $v\in S_Q$ and $\alpha\in\mathrm{Fin}\,m$, and remainders $W'_\alpha$ on $G$, subject to: `hblind`, each $W'_\alpha$ is invariant under right translation by `placeEmbed ℚ v x` for every $v\in S_Q$ and every $x\in GL_2(\mathbb{Q}_v)$; `hwlaw`, each slot satisfies $w_{v,\alpha}(u(x)g)=\psi_{\mathbb{Q},v}(x)\,w_{v,\alpha}(g)$ with $u(x)=$ [`UnramifiedWhittaker.unipotent x`](def/UnramifiedWhittaker_HeckeRecursion.html#L23) and $\psi_{\mathbb{Q},v}=$ [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65); `hWlaw`, for every adele $t$ with vanishing archimedean component such that `unipotentGL2 t` has trivial local component at every $v\in S_Q$, $W'_\alpha(\mathrm{unipotentGL2}(t)\,g)=\mathrm{psiQ}(t)\,W'_\alpha(g)$; `hwmeas` and `hWmeas`, measurability of each $w_{v,\alpha}$ for the local Borel structure and of $g\mapsto W'_\alpha(g)$ on $G_f$; `hwsm`, for each $v\in S_Q$ and $\alpha$ there is an open subgroup $U\le GL_2(\mathbb{Q}_v)$ with $w_{v,\alpha}(gk)=w_{v,\alpha}(g)$ for all $k\in U$; `hWK`, each $W'_\alpha$ is right invariant under every $k\in G_f$ whose local component lies in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) at every $v\notin S_Q$ and is trivial at every $v\in S_Q$; and `hsplitW`, the splitting
--   $$W_{f0}(\mathrm{finFactor}(g))=\sum_{\alpha}\Big(\prod_{v\in S_Q}w_{v,\alpha}(\mathrm{localAt}\ v\ g)\Big)\,W'_\alpha(g)\qquad (g\in G).$$
--
--   Purifier and measure data. Integers and elements $n_P$, $c_P:\mathrm{Fin}\,n_P\to\mathbb{C}$, $x_P:\mathrm{Fin}\,n_P\to GL_2(\mathbb{Q}_p)$ are given. Measure data consists of a Haar measure $\mu_{fH}$ on $G_f$, a Haar measure $\mu_{NF}$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), and for every finite place $v$ a measure $\mu_v$ on $GL_2(\mathbb{Q}_v)$ and a measure $\mu_{N,v}$ on the range of `unipotentGL2Hom` over $\mathbb{Q}_v$, both for the local Borel structures, with `hμv` requiring $\mu_v$ and $\mu_{N,v}$ to be Haar measures for every $v\in S_Q$; the adelic group is assumed second countable.
--
--   Conclusion. There exists $c\in\mathbb{C}$ with $c\neq 0$ such that the following holds for every frozen $GL_3$ translate and every combination datum, the constant $c$ thus being independent of them and of $s$. Let $h_3^f\in GL_3(\mathbb{A})$ have trivial archimedean component, trivial component at $p$, and trivial component at every $v\notin S_Q$; let $m_3\in\mathbb{N}$, $d:\mathrm{Fin}\,m_3\to\mathbb{C}$ and $k:\mathrm{Fin}\,m_3\to GL_3(\mathbb{A})$ be such that each $k_j$ has trivial archimedean component and trivial component at every $v\neq p$; and let $s\in\mathbb{C}$. Put, for $y\in GL_3(\mathbb{Q}_p)$,
--   $$W_3(y)=\sum_j d_j\,\chi_{A,p}\big(\det(y\,k_{j,p})\big)\,W_{F,p}(y\,k_{j,p}),$$
--   where $k_{j,p}=$ `componentAt3 (𝓞 ℚ) ℚ p (k j)`, $\chi_{A,p}=$ `localChar χA p` and $W_{F,p}=$ `F.whittakerLoc p`; put, for $y\in GL_2(\mathbb{Q}_p)$,
--   $$\tilde u_\beta(y)=\sum_j c_{P,j}\,\big(\mathrm{detNorm}(\mathrm{placeEmbed}\ \mathbb{Q}\ p\ x_{P,j})\big)^{-1/2} w_{p,\beta}(y\,x_{P,j});$$
--   and put, for $v'\in S_Q$ with $v'\neq p$ and $y\in GL_2(\mathbb{Q}_{v'})$,
--   $$\Phi_{v'}(y)=\chi_{A,v'}\big(\det(\mathrm{iotaGL}(y)\,h^f_{3,v'})\big)\,W_{F,v'}\big(\mathrm{iotaGL}(y)\,h^f_{3,v'}\big),\qquad h^f_{3,v'}=\mathrm{componentAt3}\ (\mathcal{O}_{\mathbb{Q}})\ \mathbb{Q}\ v'\ h_3^f.$$
--   Assume the two integrability hypotheses, both with respect to $\mu_v$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the local unipotent range and $\mu_{N,v}$: for every $\beta$ the function $g\mapsto W_3(\mathrm{iotaGL}(g))\,\tilde u_\beta(g)\,\mathrm{modulus}(\det g)^{s-1/2}$ is integrable on $GL_2(\mathbb{Q}_p)$; and for every $\beta$ and every $v'\in S_Q$ with $v'\neq p$ the function $g\mapsto \Phi_{v'}(g)\,w_{v',\beta}(g)\,\mathrm{modulus}(\det g)^{s-1/2}$ is integrable on $GL_2(\mathbb{Q}_{v'})$.
--
--   Then, writing $E$ for the cut
--   $$E=\{g\in G_f:\ \forall v\notin S_Q,\ \mathrm{localAt}\ v\ g=n\,k\ \text{for some }n\in(\mathrm{unipotentGL2Hom})\text{-range over }\mathbb{Q}_v\text{ and }k\in \mathrm{localLevelOne}\ (\mathcal{O}_{\mathbb{Q}})\ \mathbb{Q}\ v\ \top\},$$
--   for the purified vector
--   $$W^{+}(g)=\sum_j c_{P,j}\big(\mathrm{detNorm}(\mathrm{placeEmbed}\ \mathbb{Q}\ p\ x_{P,j})\big)^{-1/2}\,W_{f0}\big(\mathrm{finFactor}(\mathrm{finFactor}(g)\cdot \mathrm{placeEmbed}\ \mathbb{Q}\ p\ x_{P,j})\big),$$
--   and for the frozen $GL_3$ vector
--   $$F_f(g)=W_3\big(\mathrm{iotaGL}(\mathrm{localAt}\ p\ \mathrm{finFactor}(g))\big)\cdot\prod_{v}^{\mathrm{f}}\Big(\text{1 if }v=p,\ \text{else } \chi_{A,v}\big(\det(\mathrm{iota}(\mathrm{finFactor}(g))_v\,h^f_{3,v})\big)\,W_{F,v}\big(\mathrm{iota}(\mathrm{finFactor}(g))_v\,h^f_{3,v}\big)\Big),$$
--   the product being the finitely supported product `∏ᶠ` over all finite places, the identity
--   $$\mathrm{rsFinIntegral}\ \mu_{fH}\ \mu_{NF}\ s\ \big(\mathbf{1}_E\cdot W^{+}\big)\ \big(\mathbf{1}_E\cdot F_f\big)\;=\;c\cdot\sum_\beta W'_\beta(1)\cdot \Psi_p\big(s;\tilde u_\beta,\,W_3\circ\mathrm{iotaGL}\big)\cdot\prod_{v'\in S_Q\setminus\{p\}}\Psi_{v'}\big(s;w_{v',\beta},\Phi_{v'}\big)$$
--   holds. Here the left‑hand side is [`RSCarrier.rsFinIntegral`](def/LanglandsTunnell_RSCarrier.html#L46), namely the integral over $G_f$ of the product of the two cut functions against $\mathrm{ideleNorm}(\det)^{s-1/2}$ with respect to $\mu_{fH}$ weighted by the [`HaarQuotient.density`](def/HaarQuotient.html#L25) of `finUnipotent` and $\mu_{NF}$, and $\Psi_v(s;W,\Phi)$ denotes [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) for $\mu_v$, the local unipotent range, $\mu_{N,v}$, the modulus function $g\mapsto \mathrm{modulus}(\det g)$ and the exponent $s-1/2$, the local factor at $v'$ using the slot $w_{v',\beta}$ indexed through the inclusion $S_Q\setminus\{p\}\subseteq S_Q$.
--
--   This is the Euler factorisation of the cut finite Rankin–Selberg integral of a $GL_2$ test vector against the Whittaker vector of the $GL_3$ form induced from the cubic field $K$: the global integral over the finite adelic group, restricted to the big‑cell cut away from $S_Q$, is evaluated as a nonzero measure constant times a sum over the splitting index of local Rankin–Selberg integrals at $p$ and at the remaining places of $S_Q$. It feeds the non‑vanishing argument [`LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch`](thm.html#LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch), where the factorised right‑hand side is used to produce translates with nonvanishing cut integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQram : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFw : ∀ v, Continuous (F.whittakerLoc v))
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)

    (Wf0 : finiteAdelicGL2Subgroup ℚ → ℂ)
    (m : ℕ) (w : ∀ v : ↥SQ, Fin m → GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hblind : ∀ (α : Fin m) (v : ↥SQ) (x : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W' α (g * UnramifiedWhittaker.placeEmbed ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g)
    (hwlaw : ∀ (v : ↥SQ) (α : Fin m) (x : (v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w v α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (v : HeightOneSpectrum (𝓞 ℚ)) x * w v α g)
    (hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ v : ↥SQ, localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g)
    (hwmeas : ∀ (v : ↥SQ) (α : Fin m), letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); Measurable (w v α))
    (hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (hwsm : ∀ (v : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w v α (g * k) = w v α g)
    (hWK : ∀ (α : Fin m) (k : finiteAdelicGL2Subgroup ℚ),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g)
    (hsplitW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf0 (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ v : ↥SQ, w v α (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g)

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μfH : Measure (finiteAdelicGL2Subgroup ℚ)) [μfH.IsHaarMeasure]
    (μNF : Measure RSCarrier.finUnipotent) [μNF.IsHaarMeasure]

    (μv : ∀ v : HeightOneSpectrum (𝓞 ℚ), @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μNv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    (hμv : ∀ v ∈ SQ,
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      (μv v).IsHaarMeasure ∧ (μNv v).IsHaarMeasure) :
    ∃ c : ℂ, c ≠ 0 ∧

      ∀ (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ),
        (archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) →
      ∀ (m₃ : ℕ) (d : Fin m₃ → ℂ) (k : Fin m₃ → AdelicGL 3 (𝓞 ℚ) ℚ),
        (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) →
      ∀ s : ℂ,

        (∀ β : Fin m, (letI := localGLBorel ℚ p
          haveI := borelSpace_localGLBorel ℚ p
          Integrable (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
            ((fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y)) g * (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv p).withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p))))) →

        (∀ (β : Fin m) (v' : ↥SQ), (v' : HeightOneSpectrum (𝓞 ℚ)) ≠ p →
          (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
          haveI := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
          Integrable (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
            ((fun y : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) g * (w v' β) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv (v' : HeightOneSpectrum (𝓞 ℚ))).withDensity (HaarQuotient.density (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ))))))) →
        RSCarrier.rsFinIntegral μfH μNF s
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
            ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) =
          c * ∑ β : Fin m, W' β 1 *
            ((letI := localGLBorel ℚ p
            RSCarrier.rsLocalIntegral (μv p) (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p)
              (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ))
              s (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y))) *
              ∏ v' : ↥(SQ.erase p),
                (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
            RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun y : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) (iotaGL y * componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f)))) := by sorry
