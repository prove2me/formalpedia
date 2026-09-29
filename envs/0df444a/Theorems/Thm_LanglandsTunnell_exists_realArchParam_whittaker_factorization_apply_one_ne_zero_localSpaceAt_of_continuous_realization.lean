-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization
-- name    : LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/128c9e74-1833-53ad-b7ab-e0d40a7072ed
-- title:
--   Archimedean parameters and Whittaker factorisation of a cusp realisation over ℚ
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a level ideal of $\mathcal{O}_\mathbb{Q}$ that is non-zero, together with families $a,b$ indexed by the primes), and let $R$ be a smooth cusp realisation at the pins `productionPinsGeneral ℚ` of the rescaled eigensystem `Φ.toRawCentral` (same level and same $a$, with $b_v$ divided by the absolute norm of $v$): thus $R$ consists of a nowhere-identically-zero function on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, a central character `R.centralChar` on the group `pins.Z`, smoothness and cuspidality, invariance under the level subgroup, a finite exceptional set `R.exceptionalSet`, and Hecke and central eigenvalue properties off that set; assume moreover that `R.toFun` is continuous. The assertion is the existence of a finite set $S$ of primes containing `R.exceptionalSet`, of a parameter $\mathrm{archR}(w)\in$ `RealArchParam` for each real place $w$, and of a function $C$ of a finite idele and an adelic group element, such that: $C(1,1)\neq 0$; whenever $\mathrm{archR}(w)$ is principal with data $(u_1,a_1,u_2,a_2)$ one has $|\mathrm{Re}(u_1-u_2)|<1$, and if $u_1-u_2=p$ for a non-zero integer $p$ then $a_1-a_2\neq p+1$ in $\mathbb{Z}/2$; for each real $w$ the character `R.centralChar`, transported to the full idele unit group along `Subgroup.topEquiv.symm`, has archimedean component at $w$ given by $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,(e+1)}(x/\|x\|)^{a}$ with $e$ the central exponent and $a$ the value in $\{0,1\}$ of the central sign of $\mathrm{archR}(w)$; and, for every choice of parity function $\mathrm{par}$ on the infinite places, there are a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, real profiles $W_w:\mathbb{C}\to\mathbb{C}$ and weights $k(w)\in\mathbb{Z}$ with the following properties. First, $\varphi$ is a non-zero isotypic cusp form in the sense of `IsIsotypicCuspFormAt` for the pins, the central character `R.centralChar`, the level of $\Phi$, the set $S$ and $\Phi$ (smooth cuspidal automorphic, continuous, right invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Phi.a_v$ and a central eigenfunction with eigenvalue $(\Phi.\mathrm{toRawCentral}).b_v$ for every $v\notin S$). Second, at every prime $p$ the local Whittaker space `WhittakerModel.localSpaceAt` of $\varphi$ at $p$ with respect to $\psi_\mathbb{Q}$ — the span of the restrictions to $\mathrm{GL}_2(\mathbb{Q}_p)$ of the first Whittaker coefficients of the right translates of $\varphi$ — is irreducible (any non-zero member generates it under right translation), admissible (for each open subgroup $U$ a single finite set spans the $U$-invariant members) and smooth (each member is invariant under some open subgroup). Third, $\varphi$ is reproduced by right convolution against some test function $\alpha$ that is factorizable, i.e. a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor. Fourth, at each real place $w$ the form $\varphi$ satisfies `HasArchCharacterAt₀` for the character `archWeightCharAt hw (k w)`, the $k(w)$-th power of the standard weight-one character of the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2$ over the completion at $w$; the weight is pinned down by $k(w)=\mathrm{signShift}(a_1+\mathrm{par}(w))+\mathrm{signShift}(a_2+\mathrm{par}(w))$ in the principal case and $k(w)=n+1$ in the discrete case with data $(u_0,n)$, $n\geq 1$. Fifth, for every idele unit $a$ and every $g$ in the kernel of the archimedean projection, the first Whittaker coefficient of $\varphi$ at $\mathrm{diag}(a,1)\,g$ equals $\bigl(\prod_{w}W_w(a_\infty\text{ at }w)\bigr)\,C(a_{\mathrm{fin}},g)$, the product being over all infinite places. Sixth, in the principal case with $a_1=a_2$ and $\mathrm{par}(w)=a_1$ one has $W_w(-t)=(-1)^{a_1}W_w(t)$ for all real $t$; in the discrete case $W_w(t)=0$ for $t<0$. Finally, two Mellin identities: in the principal case with $a_1=a_2$ and $\mathrm{par}(w)=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_w(t)+(-1)^{a_1}W_w(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $\mathrm{archR}(w)$ twisted by $(0,a_1)$ at $s$; and for every $b\in\mathbb{Z}/2$ equal to $\mathrm{par}(w)$ or to $\mathrm{par}(w)$ plus the central sign, the analogous Mellin transform with $(-1)^{b}$ converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $\mathrm{archR}(w)$ twisted by $(0,b)$ at $s$.
--
--   This assembles the archimedean data and the Whittaker-coefficient factorisation attached to a continuous smooth cusp realisation over $\mathbb{Q}$, in the form required as input to the converse theorem in the Langlands–Tunnell step: the local Whittaker spaces at all primes are irreducible, admissible and smooth, and the finite Whittaker factor is non-zero at the identity. It is used in the construction of the unitary shaped vector with its torus profile and of the Rankin–Selberg datum with prescribed archimedean components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
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

theorem LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
      (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      R.exceptionalSet ⊆ S ∧
      C 1 1 ≠ 0 ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ)) ∧
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
