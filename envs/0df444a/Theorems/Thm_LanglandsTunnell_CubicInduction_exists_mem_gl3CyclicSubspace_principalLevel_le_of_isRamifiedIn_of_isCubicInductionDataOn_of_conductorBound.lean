-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound
-- name    : LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/4d55bd3c-c022-5b06-a3f1-4e3017aad9d9
-- title:
--   Congruence-invariant vector in the local cyclic space at a ramified bad place
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb{Q}]=3$ (hypothesis `hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$.
--
--   **Global characters.** $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ with `IsGlobalAddChar`, i.e. trivial on the image of $\mathbb{Q}$, continuous and non-trivial; `hlev` requires in addition that at every finite place $v$ of $\mathbb{Q}$ the local component $\psi_v$ obtained by composing $\psi$ with the inclusion of $v$-adic numbers into the adeles has `addCharLevel` equal to $0$. $\mu$ is a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ which is an admissible twist (`hμ`): trivial on principal ideles, continuous and of absolute value $1$. Its archimedean components are pinned by `huR` and `huC`: for each real place $w$ of $K$ the component of $\mu$ at $w$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,u_R(w)}\,(x/\|x\|)^{(a_R(w)).\mathrm{val}}$ with $a_R(w)\in\mathbb{Z}/2$, and for each complex place $w$ it is the analogous expression with exponents $u_C(w)\in\mathbb{C}$ and $k_C(w)\in\mathbb{Z}$. The hypothesis `hns` asserts that $\mu$ is not obtained by base change: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and whose contraction $\mathfrak{p}=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is a place where $\eta$ is unramified, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{\mathfrak{p}})^{f(\mathfrak{P}/\mathfrak{p})}$ for the uniformizer ideles and the inertia degree $f$.
--
--   **Carrier data and bad places.** $D$ is a subset of the adelic $\mathrm{GL}_2$ over $\mathbb{Q}$, $U$ a family of subgroups of it indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$, and `gen` a family of adelic $\mathrm{GL}_2$ elements indexed by finite places; these are assembled by `productionPinsOf` into the carrier pins with the Borel structure and Haar measure on adelic $\mathrm{GL}_2$, full central subgroup, and the additive adelic Haar measure conditioned on `AdelicBox.adelicBox ℚ`. $S$ is a finite set of finite places of $\mathbb{Q}$ which by `hS` consists exactly of the bad places of $(K,\mu)$, that is the places ramified in $K$ together with those under a prime at which $\mu$ is ramified.
--
--   **The datum.** $X$ is a `CubicInductionData`: a form on adelic $\mathrm{GL}_3$ over $\mathbb{Q}$, a Whittaker function, local Whittaker functions $W_v$ on $\mathrm{GL}_3$ of the $v$-adic completions, an archimedean Whittaker function, a central character, and a dual Whittaker function. The hypothesis `hX` states `IsCubicInductionDataOn` for $(K,\text{pins},\psi,\mu,S,X)$; its clauses (left-automorphy under $\mathrm{GL}_3(\mathbb{Q})$, transformation under the centre through `X.centralChar`, triviality of that character on principal ideles, cuspidality along the two maximal parabolics, identification of `X.whittaker` with the $\psi$-Whittaker integral of the form and its $\psi$-Whittaker transformation law, the mirabolic expansion summing to the form, the $\psi_v$-Whittaker law and factorisation of the Whittaker function into the archimedean factor times the local factors over any finite set containing $S$, sphericity of the induced type and level invariance off $S$, local multiplicity one, moderate growth, $K_\infty$-finiteness, iota moments, Whittaker half-plane, and the corresponding clauses for the dual Whittaker function attached to $\psi^{-1}$ and the dual form) are summarised here.
--
--   Further analytic hypotheses on the datum: continuity of the form, of the Whittaker function and of the dual Whittaker function (`hcont`, `hcontW`, `hcontW'`); gauge majorisation `IsGaugeMajorised3` of the Whittaker function and of its dual (`hW`, `hW'`), i.e. vanishing outside a root-level region and, for each $N$, a bound by a constant divided by $\mathrm{rootSizeProd}^t(1+\mathrm{archRootSum})^N$; non-vanishing of the archimedean Whittaker function (`hne`).
--
--   **Local hypotheses at $S$.** For each $w\in S$, `hatS` requires: $W_w(1)=1$; every non-zero $F$ in the cyclic subspace $\langle W_w\rangle$ (the span of the right translates of $W_w$) generates $W_w$ back, $W_w\in\langle F\rangle$; $W_w$ is right-invariant under some open subgroup; and for every open subgroup $U_w$ there is a finite set $B$ of functions such that every $U_w$-right-invariant member of $\langle W_w\rangle$ lies in the span of $B$. For each $w \in S$, `hcent` requires the local component of `X.centralChar` at $w$ to be unitary and $W_w(\mathrm{scalar}(t)\,h)=\omega_w(t)W_w(h)$.
--
--   **Conductor bounds on the central character.** `hωcond`: at every finite place $v$ of $\mathbb{Q}$ not ramified in $K$, the local component of `X.centralChar` has a conductor exponent $a$ with $a\le \mathrm{inducedLevelAt}\,K\,\mu\,v=\sum_{w\mid v} f(w/v)\,c(\mu_w)$. `hωcondR`: at every finite place $v$ there is a conductor exponent $a$ of that local component with $a\le \sum_{w\mid v} f(w/v)\,\mathrm{pinnedExp}(K,\mu,w)$, where $\mathrm{pinnedExp}(K,\mu,w)=c(\mu_w)+\mathrm{addCharLevel}(\psi^{\mathrm{st}}_{K,w})$.
--
--   **Archimedean splitting, scaling and measures.** $E$ is a homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the ideles with `hE`: $E(u)$ has infinite part $u$ and finite part $1$. $a\in\mathbb{Q}^\times$, $a_\infty$ is the infinite idele unit with underlying element the image of $a$, and $\psi_\infty$ is the additive character $x\mapsto \mathrm{psiArch}(a\,x)$ of the infinite adeles (`hpsiInf`), which by `hψinf` is the restriction of $\psi$ to the infinite part. The infinite adele ring and its unit group carry Borel measurable structures; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the push-forward of Lebesgue volume along the inverse of the mixed-space ring equivalence (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units.
--
--   **The archimedean package `hArch`** is a conjunction of five clauses concerning $W_\infty=$ `X.whittakerArch`:
--   1. $W_\infty$ is continuous and there is $t\in\mathbb{N}$ such that for every $N$ there is $C$ with $\|W_\infty(g_\infty)\|\le C/\bigl((\prod_{w}\mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t(1+\mathrm{archRootSum}(g))^N\bigr)$ for all $g$ in adelic $\mathrm{GL}_3$;
--   2. $W_\infty$ satisfies the $\psi_\infty$-Whittaker law $W_\infty(u(x,y,z)g)=\psi_\infty(x+y)W_\infty(g)$ for upper unipotent $u(x,y,z)$;
--   3. $W_\infty(\mathrm{scalar}(z)g)=\mathrm{centralChar}(E z)\,W_\infty(g)$;
--   4. for every admissible twist $\sigma$ of $\mathbb{Q}$, every $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ pinning the components of $\sigma$ at the real places of $\mathbb{Q}$, and every $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, there is an entire function $P$ such that: (a) for some $\sigma_0$ the zeta integral `archZeta30` of $h\mapsto W_\infty(h g_\infty)$ against $\sigma\circ E$ converges for $\mathrm{Re}\,s>\sigma_0$ and equals $P(s)$ times the archimedean factor of the Hecke $L$-datum $\mathrm{heckeDatum}\,K\,\mu$ with parameters $(u_R+t,\,a_R+e,\,u_C+t,\,k_C)$; (b) on every vertical strip $P$ is bounded by $C\exp(A|\mathrm{Im}\,s|)$; (c) on every vertical strip and for every $N$ the product $|\mathrm{Im}\,s|^N\|P(s)\cdot\mathrm{archFactor}(s)\|$ is bounded for $|\mathrm{Im}\,s|$ large; (d) for some $\sigma_1$ the dual zeta integral converges in the sense of `IsArchZeta31ConvergentAbove` for the dual Whittaker function, the inverse character and the point $\mathrm{weylPrime3}\cdot\mathrm{transposeInv3}(1)$, and for $\mathrm{Re}(1-s)>\sigma_1$ one has
--   $$\mathrm{archZetaDual31}(1-s)=\Bigl(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(a_R(w)+e)\cdot\prod_{w\ \mathrm{complex}}i^{|k_C(w)|}\cdot\prod_{w\mid\infty}\lambda_{\mathrm{arch}}(K,w)\Bigr)\bigl(\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3\bigr)\,|a|^{3(s-1/2)}\,P(s)\,\mathrm{archFactorDual}(1-s);$$
--   5. there exist an admissible twist $\sigma$ of $\mathbb{Q}$ and $s\in\mathbb{C}$ with `archZeta30` $\nu_{\mathrm{mul}}$ $W_\infty$ $(\sigma\circ E)$ $s$ $1$ non-zero.
--
--   **Conclusion.** For every $v\in S$ which is ramified in $K$ (i.e. some prime above $v$ has ramification index $\neq 1$), and every $e\in\mathbb{N}$ which is a conductor exponent of the local component of `X.centralChar` at $v$, there exists $W$ in the cyclic subspace $\langle W_v\rangle$ spanned by the right translates of $W_v$ such that:
--
--   - $W\neq 0$;
--
--   - if $\mathrm{addCharLevel}(\psi_v)=0$ then $W(1)=1$;
--
--   - there exists $N\in\mathbb{N}$ with the following two properties. First, for every $M\in\mathbb{N}$ such that each prime $w$ above $v$ admits a conductor exponent $a_w\le M$ for the local component of $\mu$ at $w$, one has the inequality of integers
--   $$N\ \le\ 2\Bigl(\sum_{w\mid v} f(w/v)\bigl[e(w/v)\,(2(48+e+M)+d_w+2)+M+d_w+1\bigr]\ +\ (48+e+M)\Bigr),$$
--   where $f(w/v)$ and $e(w/v)$ are the inertia degree and ramification index of $w$ over $v$ and $d_w=\mathrm{addCharLevel}(\psi^{\mathrm{st}}_{K,w})$. Second, $W$ is right-invariant under the principal congruence subgroup of level $N$: for every $k$ in `localMaximalCompact3` at $v$ all of whose entries satisfy $v(k_{ij}-\delta_{ij})\le \exp(-N)$, and every $g$, one has $W(gk)=W(g)$.
--
--   This is the local step at the ramified bad places in the converse-theorem construction of the cubic induction (Langlands–Tunnell) automorphic form on $\mathrm{GL}_3$ over $\mathbb{Q}$: from the global datum and its archimedean functional equation one extracts, inside the cyclic space generated by the local Whittaker function at a place $v$ ramified in $K$, a non-zero vector normalised at the identity and invariant under a principal congruence subgroup whose level is bounded explicitly in terms of the conductor of the central character, the conductors of $\mu$ above $v$, and the local ramification data. It is used in the assembly of the cubic induction data with prescribed archimedean, torus and local behaviour at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (hωcondR : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ a : ℕ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a ∧
      (a : ℤ) ≤ ∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)
 :
    ∀ v ∈ S, IsRamifiedIn K v →
      ∀ e : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (NumberField.TateGlobal.localChar X.centralChar v) e →
      ∃ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 ∧
        (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 → W 1 = 1) ∧
        ∃ N : ℕ,
          (∀ M : ℕ, (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
              LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) aw) →
            (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
                ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                  ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                      (2 * ((48 : ℤ) + e + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                    M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
              ((48 : ℤ) + e + M))) ∧
          ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
            (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
                (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
            ∀ g : LocalGL3 v, W (g * k) = W g := by sorry
