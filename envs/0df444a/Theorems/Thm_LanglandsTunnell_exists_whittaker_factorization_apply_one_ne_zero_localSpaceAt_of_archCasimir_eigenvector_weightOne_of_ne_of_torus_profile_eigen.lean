-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen
-- name    : LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/fb7f106c-5747-5456-8571-08f7cddaca77
-- title:
--   Weight-one Whittaker factorisation over the torus fibre
-- statement:
--   Fix a complex Hecke eigensystem $\Phi$ for $\mathbb{Q}$ (a nonzero level ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with coefficient families `Φ.a`, `Φ.b` indexed by the primes of $\mathcal{O}_{\mathbb{Q}}$), and let $R$ be a smooth cusp realisation, at the general production pins `productionPinsGeneral ℚ` (the Siegel-set carrier data with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$, level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, Hecke generators `heckeGen` and the adelic box), of the rescaled eigensystem `Φ.toRawCentral`, whose central coefficients are $b_v$ divided by the absolute norm of $v$. Thus $R$ carries a nonvanishing function `R.toFun` on $\mathrm{GL}_2$ of the adeles, a central character `R.centralChar` on the pins' central subgroup, the smooth-cusp and level-invariance properties, a finite exceptional set `R.exceptionalSet`, and the Hecke-coset and central eigenvalue relations for `Φ.a` and `Φ.toRawCentral.b`. It is assumed that `R.toFun` is continuous. Further data: a finite set $S$ of primes containing `R.exceptionalSet`; an assignment $w \mapsto \mathrm{archR}\,w$ of an element of `RealArchParam` to each real infinite place $w$ of $\mathbb{Q}$; a function $\varphi_1$ on $\mathrm{GL}_2$ of the adeles with values in $\mathbb{C}$; a family of integers $k_1(w)$; a family of complex scalars $c_0(w)$; and a $\mathbb{C}$-submodule $V$ of functions on $\mathrm{GL}_2$ of the adeles.
--
--   The hypotheses on $\mathrm{archR}$ are: for every principal value $\mathrm{archR}\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ one has $|\mathrm{Re}(u_1-u_2)| < 1$; and, at each real $w$, the predicate `IsArchCompAt` holds for the character obtained from `R.centralChar` by transport along `Subgroup.topEquiv.symm`, with exponent $e(\mathrm{archR}\,w)+1$ and sign exponent the value in $\{0,1\}$ of $\epsilon(\mathrm{archR}\,w)$, where $e$ and $\epsilon$ are `RealArchParam.centralExponent` and `RealArchParam.centralSign`; concretely, for every unit $x$ of the completion at $w$ the $w$-component of the central character equals $\|x\|^{m_w(e+1)}\,(\iota_w(x)/\|x\|)^{\epsilon}$, with $m_w$ the multiplicity of $w$ and $\iota_w$ the embedding `extensionEmbedding w`.
--
--   The hypotheses on $\varphi_1$ are: it is an isotypic cusp form at the production pins with central character `R.centralChar`, level $\Phi.\mathrm{level}$ and exceptional set $S$ for $\Phi$ (that is, `IsIsotypicCuspFormAt`: smooth cuspidal automorphic, continuous, invariant under the level subgroup, a Hecke-coset eigenfunction with eigenvalue $\Phi.a_v$ for $v \notin S$, and central eigenfunction with eigenvalue $(\mathrm{absNorm}\,v)^{-1}\Phi.b_v$ for $v \notin S$); it is nonzero; it is reproduced by right convolution, $\mathrm{rightConv}\,\varphi_1\,\alpha = \varphi_1$, for some factorizable test function $\alpha$ (a product of a smooth compactly supported archimedean factor with a locally constant compactly supported finite factor); at each real $w$ it satisfies the archimedean weight condition `HasArchCharacterAt₀` for the character `archWeightCharAt hw (k₁ w)`, the $k_1(w)$-th power of the weight-one character at $w$; the weights match the parameters, in the sense that for a principal $\mathrm{archR}\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ one has $k_1(w) \in \{0,1\}$ and $k_1(w) \equiv a_1+a_2 \pmod 2$, while for a discrete $\mathrm{archR}\,w = \mathrm{discrete}\,u_0\,n$ with $n \ge 1$ one has $k_1(w) = n+1$; at each real $w$ the form is archimedean-smooth (`IsArchSmoothAt`) and a Casimir eigenfunction, $\mathrm{archCasimirAt}\,\varphi_1 = \lambda(\mathrm{archR}\,w)\cdot\varphi_1$ with $\lambda$ the eigenvalue `RealArchParam.laplaceEigenvalue`; and at each real $w$ the parameter $\mathrm{archR}\,w$ is principal, $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, with $a_1 \ne a_2$ and $u_1 \ne u_2$.
--
--   The torus-fibre hypotheses are: $c_0(w)^2 = 1 - 4\lambda(\mathrm{archR}\,w)$ at each real $w$; and, writing $L\varphi_1 = D_H\varphi_1 - i\,(D_E\varphi_1 + D_{F^-}\varphi_1)$ for the archimedean directional derivatives `archDerivAt` at $w$, for every $g$ with trivial finite part (i.e. $\mathrm{glFin}\,g = \mathrm{glFin}\,1$) the Whittaker coefficient at $\alpha = 1$ for the standard additive character `psiQ` of the right translate $x \mapsto (L\varphi_1)(x \cdot \mathrm{archRealGLAt}\,hw\,J)$, evaluated at $g$, equals $c_0(w)$ times the Whittaker coefficient of $\varphi_1$ at $\alpha = 1$ and $g$; here $J$ is `UpperHalfPlane.J`.
--
--   The constituent hypotheses are: $V$ is a cuspidal constituent for the production pins and `R.centralChar` (`IsCuspConstituent`: a cusp subrepresentation contained in the $K$-finite cusp module and stable under right translation by elements of trivial archimedean part, under right translation by rotations at each infinite place and under right convolution with archimedean-bi-finite factorizable test functions, nonzero, and minimal among such subrepresentations); $\varphi_1 \in V$; and each $\varphi \in V$ has, at every prime $p$, a local $\mathrm{psiQ}$-Whittaker space `WhittakerModel.localSpaceAt` which is irreducible in the sense that every nonzero $W_0$ in it has right translates $g \mapsto W_0(gh)$ spanning it, admissible in the sense that for every open subgroup $U$ of $\mathrm{GL}_2$ of the completion at $p$ there is a finite set $B$ of functions spanning all $U$-invariant members, and smooth in the sense that every member is invariant under some open subgroup. Finally, the torus-profile hypothesis requires an idele unit $a$ with trivial finite part, $(a)_2 = 1$, such that the Whittaker coefficient of $\varphi_1$ at $\alpha = 1$ and $\mathrm{diagOne}\,a = \mathrm{diag}(a,1)$ is nonzero.
--
--   The conclusion asserts the existence of a second assignment $\mathrm{archR}'$ of a `RealArchParam` to each real place such that the following five items hold. First, at each real $w$ either $\mathrm{archR}'\,w = \mathrm{archR}\,w$, or $\mathrm{archR}\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ and $\mathrm{archR}'\,w = \mathrm{principal}\,u_1\,a_2\,u_2\,a_1$ (the two signs interchanged). Second, $\mathrm{archR}'$ satisfies the same bound: $|\mathrm{Re}(u_1-u_2)| < 1$ for every principal value. Third, a genericity clause: if $\mathrm{archR}'\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, then for every nonzero integer $p$ with $u_1-u_2 = p$ one has $a_1 - a_2 \ne p+1$ in $\mathbb{Z}/2$. Fourth, the central-character compatibility `IsArchCompAt` holds at each real $w$ for the transported `R.centralChar` with exponent $e(\mathrm{archR}'\,w)+1$ and sign exponent $\epsilon(\mathrm{archR}'\,w)$.
--
--   Fifth, there is a function $C$ of a finite adele and a group element, with $C\,1\,1 \ne 0$, such that for every parity function $\mathrm{par}$ from the infinite places to $\mathbb{Z}/2$ there exist a function $\varphi$ on $\mathrm{GL}_2$ of the adeles, a family of functions $W_w : \mathbb{C} \to \mathbb{C}$ indexed by the infinite places, and a family of integers $k(w)$, with all of the following properties. The form $\varphi$ is again an isotypic cusp form at the production pins with central character `R.centralChar`, level $\Phi.\mathrm{level}$ and exceptional set $S$ for $\Phi$, and $\varphi \ne 0$; at every prime $p$ its local `psiQ`-Whittaker space satisfies the same three clauses (generation by any nonzero vector under right translation, finite-dimensionality of the $U$-invariants for every open $U$, and invariance of each vector under some open subgroup); $\varphi$ is reproduced by right convolution with some factorizable test function; and at each real $w$ it satisfies `HasArchCharacterAt₀` for the character `archWeightCharAt hw (k w)`.
--
--   The archimedean factors are normalised by the original form: there is $\rho' \ne 0$ such that for every infinite place $w$ and every idele unit $a$ with trivial finite part, $W_w(\iota_w(a_w)) = \rho' \cdot$ (the Whittaker coefficient of $\varphi_1$ at $\alpha = 1$ and $\mathrm{diag}(a,1)$), where $a_w$ is the $w$-component of the archimedean part of $a$. The weights are prescribed by $\mathrm{archR}'$ and $\mathrm{par}$: if $\mathrm{archR}'\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ then $k(w) = \mathrm{signShift}(a_1+\mathrm{par}(w)) + \mathrm{signShift}(a_2+\mathrm{par}(w))$ as complex numbers, with $\mathrm{signShift}(0) = 0$ and $\mathrm{signShift}(1) = 1$; and if $\mathrm{archR}'\,w = \mathrm{discrete}\,u_0\,n$ with $n \ge 1$ then $k(w) = n+1$.
--
--   The factorisation itself reads: for every idele unit $a$ and every $g$ of trivial archimedean part (i.e. $g \in \mathrm{finiteAdelicGL2Subgroup}\,\mathbb{Q}$, the kernel of `glArch`),
--   $$W_\varphi(\mathrm{diag}(a,1)\cdot g) = \Big(\prod_{w \mid \infty} W_w(\iota_w(a_w))\Big)\cdot C(a_{\mathrm{fin}})(g),$$
--   where $W_\varphi$ denotes the Whittaker coefficient at $\alpha = 1$ for `psiQ` and $a_{\mathrm{fin}}$ the finite part of $a$.
--
--   Finally, the archimedean factors obey the following symmetry and Mellin relations. If $\mathrm{archR}'\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ (equal signs) and $\mathrm{par}(w) = a_1$, then $W_w(-t) = (-1)^{a_1}W_w(t)$ for all real $t$. If $\mathrm{archR}'\,w = \mathrm{discrete}\,u_0\,n$ with $n \ge 1$, then $W_w(t) = 0$ for all real $t < 0$. If $\mathrm{archR}'\,w = \mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}(w) = a_1+1$, then there is $s_0 \in \mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s > s_0$ the Mellin transform of $t \mapsto (W_w(t) + (-1)^{a_1}W_w(-t))/t$ converges at $s$ and equals
--   $$\frac{2s+u_1+u_2-1}{4\pi}\cdot \Lambda_\infty\big((\mathrm{archR}'\,w).\mathrm{twist}\,0\,a_1\big)(s),$$
--   where $\Lambda_\infty$ is the archimedean factor `RealArchParam.archFactor` and the twist adds $0$ to the exponents and $a_1$ to the signs. And for every real $w$ and every $b \in \mathbb{Z}/2$ with $b = \mathrm{par}(w)$ or $b = \mathrm{par}(w) + \epsilon(\mathrm{archR}'\,w)$, there is $s_0 \in \mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s > s_0$ the Mellin transform of $t \mapsto (W_w(t) + (-1)^{b}W_w(-t))/t$ converges at $s$ and equals $\Lambda_\infty((\mathrm{archR}'\,w).\mathrm{twist}\,0\,b)(s)$.
--
--   This is the torus-profile form of the weight-one Whittaker factorisation step in the Langlands–Tunnell route to the converse theorem: from a single nonzero Casimir eigenform of weight one, with archimedean parameter principal and regular at the real place and with a nonvanishing Whittaker value along the diagonal torus, it produces, for each choice of parity, a cusp form in the same isotypic space whose Whittaker coefficients along the torus split as a product of archimedean functions with prescribed Mellin transforms against a single finite factor, after possibly interchanging the two signs of the archimedean parameter. It feeds the downstream statement linking twisted genuine cusp realisations with the Whittaker data needed for Weil's converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen.lean

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

theorem LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen
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
    (_hne₂ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂ ∧ u₁ ≠ u₂)

    (c₀ : ∀ w : InfinitePlace ℚ, w.IsReal → ℂ)
    (_hc₀ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      c₀ w hw * c₀ w hw = 1 - 4 * (archR w hw).laplaceEigenvalue)
    (_hT₀ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ), glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ 1 →
      whittakerCoefficient ℚ
          (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (fun x => (archDerivAt hw ArchDir.H φ₁
              - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))
                (x * archRealGLAt hw UpperHalfPlane.J)) 1 g
        = c₀ w hw *
          whittakerCoefficient ℚ
            (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g)

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
    ∃ archR' : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam,
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR' w hw = archR w hw ∨
        ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧
          archR' w hw = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR' w hw).centralExponent + 1) ((archR' w hw).centralSign.val : ℤ)) ∧
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

          (∃ ρ' : ℂ, ρ' ≠ 0 ∧ ∀ (w : InfinitePlace ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
            ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
              Wr w (extensionEmbedding w (((a : AdeleRing (𝓞 ℚ) ℚ)).1 w))
                = ρ' * whittakerCoefficient ℚ
                    (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * ((archR' w hw).twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + (archR' w hw).centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = ((archR' w hw).twist 0 b).archFactor s) := by sorry
