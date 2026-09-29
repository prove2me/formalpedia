-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
-- name    : LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/4db26140-b4f8-5021-afe7-ea1f6a7340c7
-- title:
--   Weight family and Whittaker factorisation with C(1,1)≠ 0
-- statement:
--   The setting is the field $\mathbb{Q}$ with the carrier pins `productionPinsGeneral ℚ` (the production pins built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen` and the adelic box), the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) of $\mathbb{A}_\mathbb{Q}$, a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex coefficients, and a smooth cusp realization `R` at these pins for the rescaled eigensystem `Φ.toRawCentral` (same level and same Hecke eigenvalues `Φ.a`, central eigenvalues $\mathrm{N}(v)^{-1}\Phi.b(v)$): thus `R.toFun` is a nowhere-identically-zero smooth cuspidal automorphic function with central character `R.centralChar` on `pins.Z`, invariant under `pins.U Φ.level`, and a Hecke and central eigenfunction outside its finite exceptional set `R.exceptionalSet`.
--
--   The data are: the hypothesis `_hR` that `R.toFun` is continuous; a finite set $S$ of primes of $\mathbb{Q}$ with `_hS : R.exceptionalSet ⊆ S`; an assignment `archR` of a real archimedean parameter $\mathrm{archR}(w)$ — either `principal u₁ a₁ u₂ a₂` with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or `discrete u₀ n` with $n\ge 1$ — to every real infinite place $w$ of $\mathbb{Q}$; the type bound `_htype`, that $|\mathrm{Re}(u_1-u_2)|<1$ whenever $\mathrm{archR}(w)$ is principal with exponents $u_1,u_2$; and the central-character normalisation `_hcen`, stating for each real $w$ that `IsArchCompAt` holds for `R.centralChar` (transported along the inverse of `Subgroup.topEquiv`) at $w$ with exponent $\mathrm{archR}(w).\mathtt{centralExponent}+1$ and integer $\mathrm{archR}(w).\mathtt{centralSign}$, i.e. the archimedean local component of the character at $w$ sends a unit $x$ of $w$'s completion to $\|x\|^{\mathrm{mult}(w)u}\,(\iota_w(x)/\|x\|)^{a}$ with these $u$ and $a$.
--
--   Next come a function $\varphi_1$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ and weights $k_1:\{\text{infinite places}\}\to\mathbb{Z}$, subject to the following groups of hypotheses. Isotypy (`_hiso`): $\varphi_1$ is an `IsIsotypicCuspFormAt` form at the pins for the central character `R.centralChar`, level `Φ.level`, exceptional set $S$ and eigensystem $\Phi$, that is, a continuous smooth cuspidal automorphic function with that central character, right invariant under `pins.U Φ.level`, a Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ for $v\notin S$, and satisfying the central relation with eigenvalue `Φ.toRawCentral.b v` for $v\notin S$. Non-vanishing (`_hne`): $\varphi_1\neq 0$. Reproduction (`_hconv`): there is a factorizable test function $\alpha$ (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor) with `rightConv ℚ φ₁ α = φ₁`. Weight (`_hwt`): at each real place $w$, $\varphi_1$ satisfies `HasArchCharacterAt₀` for the character `archWeightCharAt hw (k₁ w)`, the $k_1(w)$-th power of the basic weight-one character of `rowIsometrySubgroup₀` at $w$. Minimality of the weight (`_hminp`, `_hmind`): if $\mathrm{archR}(w)=\mathtt{principal}\ u_1\,a_1\,u_2\,a_2$ then $k_1(w)\in\{0,1\}$ and $k_1(w)\equiv a_1+a_2 \pmod 2$; if $\mathrm{archR}(w)=\mathtt{discrete}\ u_0\,n$ then $k_1(w)=n+1$. Archimedean smoothness and Casimir eigenvalue (`_hpair`): at each real $w$, `IsArchSmoothAt hw φ₁` holds and `archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁`, the eigenvalue being $1/4-((u_1-u_2)/2)^2$ in the principal case and $(1-n^2)/4$ in the discrete case. Sign at $J$ (`_hJ`): if $\mathrm{archR}(w)$ is principal with equal parities $a_1=a_2$, then $\varphi_1(g\cdot \mathtt{archRealGLAt hw UpperHalfPlane.J})=(-1)^{a_1}\varphi_1(g)$ for all $g$. Lowering (`_hlow`, `_hlow1`): the lowering combination $\mathrm{H}\varphi_1-i(\mathrm{E}\varphi_1+\mathrm{F}\varphi_1)$ of the directional derivatives `archDerivAt hw` vanishes whenever $\mathrm{archR}(w)$ is discrete, and also whenever it is principal with equal exponents and distinct parities. Genericity (`_heq`): whenever $\mathrm{archR}(w)=\mathtt{principal}\ u_1\,a_1\,u_2\,a_2$, either $a_1=a_2$ or $u_1=u_2$.
--
--   Finally, a complex subspace $V$ of functions on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ is given with: `_hV`, that $V$ is a cuspidal constituent at the pins for `R.centralChar` in the sense of `CuspidalConstituent.IsCuspConstituent` — $V$ is a cusp subrepresentation (contained in the $K$-finite cusp submodule, stable under right translation by `finiteAdelicGL2Subgroup ℚ` and by the archimedean `rowIsometrySubgroup₀` inclusions, and under right convolution by factorizable archimedean-bi-finite test functions), $V\neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$; `_hφ₁V`, that $\varphi_1\in V$; and `_hVloc`, that for every $\varphi\in V$ and every prime $p$ the local Whittaker space [`AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ`](def/AutomorphicForm_WhittakerModelLocal.html#L19) — the span of the functions $g\mapsto$ (Whittaker coefficient at $\alpha=1$ of $x\mapsto\varphi(xh)$ evaluated at the local embedding of $g$), $h$ ranging over the adelic group — satisfies three conditions: (i) irreducibility, every nonzero $W_0$ in it generates it, in the sense that every $W$ in it lies in the span of the right translates $g\mapsto W_0(gh)$, $h\in \mathrm{GL}_2(\mathbb{Q}_p)$; (ii) admissibility, for every open subgroup $U$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ there is a finite set $B$ of functions such that every $U$-right-invariant element of the space lies in the span of $B$; (iii) smoothness, every element of the space is right invariant under some open subgroup. The last hypothesis `_htorus` provides an idele unit $a$ with trivial finite part, $a_{\mathrm{fin}}=1$, such that `whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ₁ 1 (diagOne a) ≠ 0`, where `diagOne a` is the diagonal matrix $\mathrm{diag}(a,1)$.
--
--   The conclusion asserts the existence of a single function $C$ of a finite idele and an adelic group element, $C:\mathbb{A}_{\mathbb{Q},\mathrm{fin}}\to \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$, with $C(1,1)\neq 0$, such that for every parity assignment $\mathrm{par}$ on infinite places there are a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, functions $W_w:\mathbb{C}\to\mathbb{C}$ indexed by the infinite places, and weights $k:\{\text{infinite places}\}\to\mathbb{Z}$, with the following ten properties.
--
--   First, $\varphi$ is again an `IsIsotypicCuspFormAt` form at the pins for `R.centralChar`, level `Φ.level`, exceptional set $S$ and eigensystem $\Phi$; second, $\varphi\neq 0$; third, at every prime $p$ the local Whittaker space of $\varphi$ satisfies the same three conditions (i)–(iii) as above; fourth, there is a factorizable test function $\alpha$ with `rightConv ℚ φ α = φ`; fifth, at each real place $w$ the form $\varphi$ satisfies `HasArchCharacterAt₀` for `archWeightCharAt hw (k w)`. Sixth, the weight is pinned down in the principal case: if $\mathrm{archR}(w)=\mathtt{principal}\ u_1\,a_1\,u_2\,a_2$ then $k(w)=\mathtt{signShift}(a_1+\mathrm{par}(w))+\mathtt{signShift}(a_2+\mathrm{par}(w))$ as complex numbers, where $\mathtt{signShift}(0)=0$ and $\mathtt{signShift}(1)=1$; seventh, in the discrete case $\mathrm{archR}(w)=\mathtt{discrete}\ u_0\,n$ one has $k(w)=n+1$.
--
--   Eighth, the Whittaker coefficients of $\varphi$ factorise: for every idele unit $a$ and every $g$ in `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection `glArch`),
--   $$\mathtt{whittakerCoefficient}\ \mathbb{Q}\ \mathtt{pins}\ \psi_\mathbb{Q}\ \varphi\ 1\ (\mathtt{diagOne}\ a\cdot g)=\Big(\prod_{w}W_w\big(\iota_w(a_\infty(w))\big)\Big)\cdot C(a_{\mathrm{fin}},g),$$
--   the product being over all infinite places $w$ and $\iota_w$ the embedding `extensionEmbedding w` of the completion into $\mathbb{C}$.
--
--   The remaining three conjuncts describe the archimedean factors $W_w$. Ninth, if $\mathrm{archR}(w)=\mathtt{principal}\ u_1\,a_1\,u_2\,a_1$ has equal parities and $\mathrm{par}(w)=a_1$, then $W_w(-t)=(-1)^{a_1}W_w(t)$ for all real $t$; if $\mathrm{archR}(w)=\mathtt{discrete}\ u_0\,n$, then $W_w(t)=0$ for all $t<0$. Tenth, Mellin identities: if $\mathrm{archR}(w)=\mathtt{principal}\ u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}(w)=a_1+1$, there is $s_0\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}(s)>s_0$ the Mellin transform of $t\mapsto (W_w(t)+(-1)^{a_1}W_w(-t))/t$ converges at $s$ and equals
--   $$\frac{2s+u_1+u_2-1}{4\pi}\,\big((\mathrm{archR}(w)).\mathtt{twist}\ 0\ a_1\big).\mathtt{archFactor}(s);$$
--   and for every real place $w$ and every $b\in\mathbb{Z}/2$ with $b=\mathrm{par}(w)$ or $b=\mathrm{par}(w)+\mathrm{archR}(w).\mathtt{centralSign}$, there is $s_0\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}(s)>s_0$ the Mellin transform of $t\mapsto (W_w(t)+(-1)^{b}W_w(-t))/t$ converges at $s$ and equals $\big((\mathrm{archR}(w)).\mathtt{twist}\ 0\ b\big).\mathtt{archFactor}(s)$. Here `twist 0 b` shifts both parities of a principal parameter by $b$ and leaves a discrete parameter unchanged, and `archFactor` is $\Gamma_\mathbb{R}(s+u_1+\mathtt{signShift}\,a_1)\Gamma_\mathbb{R}(s+u_2+\mathtt{signShift}\,a_2)$ in the principal case and $\Gamma_\mathbb{C}(s+u_0+n/2)$ in the discrete case.
--
--   This is the archimedean weight-family step preparing the input to the converse theorem in the Langlands–Tunnell part of the argument: starting from a minimal-weight Casimir eigenvector inside a cuspidal constituent over $\mathbb{Q}$, it produces, for each choice of parity at the infinite places, a cusp form in the same Hecke isotypic space whose Whittaker coefficients split as a product of archimedean factors times a single function $C$ of the finite data, normalised so that $C(1,1)\neq 0$, with the gamma-factor Mellin identities that the functional equations require. It specialises a version stated for arbitrary Siegel-set covering data to the production pins and the standard additive character $\psi_\mathbb{Q}$, and is used by the statements that produce a realization with a prescribed archimedean parameter and assemble the twisted genuine cusp realizations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsGeneral ℚ)
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂)

    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (_hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V) (_hφ₁V : φ₁ ∈ V)
    (_hVloc : ∀ φ ∈ V,
          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (_htorus : ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a) ≠ 0) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      C 1 1 ≠ 0 ∧
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            whittakerCoefficient ℚ
                (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
              = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
            ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                  = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                      * ((archR w hw).twist 0 a₁).archFactor s) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
          (b = par w ∨ b = par w + (archR w hw).centralSign) →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                  = ((archR w hw).twist 0 b).archFactor s) := by sorry
