-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
-- name    : LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/815b5569-d88e-50e2-879e-db3b69ccd4ee
-- title:
--   Whittaker factorisation at an odd principal archimedean parameter over ℚ
-- statement:
--   The setting is $F=\mathbb{Q}$ with the carrier pins `productionPinsGeneral ℚ`, i.e. the production pins built from the Siegel-set class representative region with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap$ `finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen`, and the adelic box.
--
--   The data are: a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with families $\Phi.a$, $\Phi.b$ indexed by the primes of $\mathcal{O}_{\mathbb{Q}}$); a smooth cusp realisation $R$ at these pins for the rescaled system $\Phi$`.toRawCentral` (same level, same $a$, and $b_v$ replaced by $N(v)^{-1}\Phi.b_v$), that is, a function $R$`.toFun` on $GL_2(\mathbb{A}_{\mathbb{Q}})$ which is nonzero somewhere, is a smooth cuspidal automorphic function for the central character $R$`.centralChar`, is right invariant under the level subgroup attached to $\Phi$`.level`, and is, outside a finite exceptional set $R$`.exceptionalSet` of primes, a Hecke coset eigenfunction with eigenvalue $\Phi.a_v$ and satisfies the central relation with eigenvalue $N(v)^{-1}\Phi.b_v$; the hypothesis `_hR` that $R$`.toFun` is continuous; a finite set $S$ of primes with $R$`.exceptionalSet` $\subseteq S$ (hypothesis `_hS`); and an assignment `archR` of a parameter `RealArchParam` to each real infinite place $w$ of $\mathbb{Q}$, each such parameter being either principal, $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ with $u_i\in\mathbb{C}$ and $a_i\in\mathbb{Z}/2$, or discrete, $\mathrm{discrete}\,u_0\,n$ with $n\ge 1$.
--
--   The hypotheses on `archR` are: `_htype`, the bound $|\mathrm{Re}(u_1-u_2)|<1$ whenever `archR w hw` is principal with exponents $u_1,u_2$; `_hcen`, that for every real $w$ the predicate `IsArchCompAt` holds for $R$`.centralChar`, viewed as a character of $\mathbb{A}_{\mathbb{Q}}^{\times}$ through the identification of the top subgroup with the full idele group, at the place $w$ with exponent (`archR w hw`)`.centralExponent` $+\,1$ and integer exponent the value of (`archR w hw`)`.centralSign` in $\mathbb{Z}/2$, i.e. the local character at $w$ of the central character is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(\iota_w(x)/\|x\|)^{a}$ with these $u$ and $a$; and `_hne₂`, that at every real place `archR w hw` is principal, $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, with $a_1\neq a_2$ and $u_1\neq u_2$.
--
--   The data also include a function $\varphi_1$ on $GL_2(\mathbb{A}_{\mathbb{Q}})$ and a family of integral weights $k_1$ indexed by the infinite places, subject to: `_hiso`, that $\varphi_1$ is an isotypic cusp form at the production pins for the central character $R$`.centralChar`, level $\Phi$`.level`, exceptional set $S$ and eigensystem $\Phi$ (a smooth cuspidal automorphic function, continuous, right invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Phi.a_v$ for $v\notin S$, and satisfying the central relation with eigenvalue $N(v)^{-1}\Phi.b_v$ for $v\notin S$); `_hne`, that $\varphi_1\neq 0$; `_hconv`, that $\varphi_1$ is reproduced by right convolution against some factorisable test function $\alpha$ (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor); `_hwt`, that for each real $w$ the predicate `HasArchCharacterAt₀` holds for $\varphi_1$ with the character `archWeightCharAt hw (k₁ w)`, the $k_1(w)$-th power of the weight-one character of the archimedean rotation subgroup `rowIsometrySubgroup₀` at $w$, so that $\varphi_1$ has weight $k_1(w)$ there; `_hminp`, that whenever `archR w hw` is principal with parities $a_1,a_2$ one has $k_1(w)\in\{0,1\}$ and $k_1(w)\equiv a_1+a_2 \pmod 2$; `_hmind`, that whenever `archR w hw` $=\mathrm{discrete}\,u_0\,n$ one has $k_1(w)=n+1$; and `_hpair`, that for each real $w$ the function $\varphi_1$ is archimedean-smooth at $w$ in the sense of `IsArchSmoothAt` (infinitely differentiable in the real matrix entries at $w$ on the locus of nonzero determinant) and satisfies $\mathrm{Casimir}_w\varphi_1=\lambda(\mathrm{archR}\,w\,hw)\,\varphi_1$, where the eigenvalue is $\tfrac14-\left(\tfrac{u_1-u_2}{2}\right)^2$ in the principal case and $\tfrac{1-n^2}{4}$ in the discrete case.
--
--   Finally, a $\mathbb{C}$-submodule $V$ of the functions $GL_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ is given with: `_hV`, that $V$ is a cuspidal constituent for the pins and $R$`.centralChar`, i.e. $V$ is a cuspidal subrepresentation (contained in the $K$-finite cusp submodule and stable under right translation by the finite-adelic subgroup, under right translation by the archimedean rotation subgroups, and under right convolution by factorisable archimedean-bifinite test functions), $V\neq 0$, and every cuspidal subrepresentation contained in $V$ is $0$ or $V$; `_hφ₁V`, that $\varphi_1\in V$; and `_hVloc`, a local Whittaker hypothesis requiring that for every $\varphi\in V$ and every prime $p$ the local Whittaker space `localSpaceAt` at $p$ for $\varphi$ and the standard character `psiQ` — the span of the functions $g\mapsto$ (first Whittaker coefficient of $x\mapsto\varphi(xh)$ at the local embedding of $g$) — is irreducible (every nonzero $W_0$ in it generates: each member lies in the span of the right translates $g\mapsto W_0(gh)$), admissible (for each open subgroup $U$ of $GL_2(\mathbb{Q}_p)$ there is a finite family $B$ of functions such that every $U$-right-invariant member of the space lies in the span of $B$), and smooth (every member is invariant under right translation by some open subgroup). The last hypothesis `_htorus` asserts the existence of a unit idele $a$ with trivial finite component whose associated diagonal element $\mathrm{diag}(a,1)$ has nonvanishing first Whittaker coefficient for $\varphi_1$ with respect to `psiQ`.
--
--   The conclusion asserts the existence of a new assignment `archR'` of a `RealArchParam` to each real place such that four clauses hold: (i) at each real $w$ either `archR' w hw` $=$ `archR w hw`, or `archR w hw` is principal $u_1\,a_1\,u_2\,a_2$ and `archR' w hw` is $\mathrm{principal}\,u_1\,a_2\,u_2\,a_1$, the two parities being exchanged while the exponents stay in place; (ii) the type bound $|\mathrm{Re}(u_1-u_2)|<1$ holds for every principal value of `archR'`; (iii) for every principal value $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ of `archR'` and every nonzero integer $p$ with $u_1-u_2=p$ one has $a_1-a_2\neq p+1$ in $\mathbb{Z}/2$; (iv) `archR'` still computes the archimedean component of the central character, namely `IsArchCompAt` holds at each real $w$ for $R$`.centralChar` with exponent (`archR' w hw`)`.centralExponent` $+\,1$ and integer exponent the value of (`archR' w hw`)`.centralSign`.
--
--   Moreover there exists a function $C$ of a finite idele and a point of $GL_2(\mathbb{A}_{\mathbb{Q}})$ with $C(1,1)\neq 0$, such that for every parity function $\mathrm{par}$ from the infinite places to $\mathbb{Z}/2$ there are a function $\varphi$ on $GL_2(\mathbb{A}_{\mathbb{Q}})$, a family $W_r$ of functions $\mathbb{C}\to\mathbb{C}$ indexed by the infinite places, and integral weights $k$ indexed by the infinite places, with all of the following. First, $\varphi$ is an isotypic cusp form at the production pins for $R$`.centralChar`, level $\Phi$`.level`, exceptional set $S$ and eigensystem $\Phi$, and $\varphi\neq 0$. Secondly, for every prime $p$ the local Whittaker space of $\varphi$ at $p$ for `psiQ` satisfies the same three conditions as in `_hVloc`: irreducibility, admissibility with respect to open subgroups, and smoothness. Thirdly, $\varphi$ is reproduced by right convolution against some factorisable test function. Fourthly, for each real $w$ the form $\varphi$ satisfies `HasArchCharacterAt₀` with the character `archWeightCharAt hw (k w)`, so it has weight $k(w)$ at $w$; the weights are pinned by the parameter: whenever `archR' w hw` is $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ one has $k(w)=\mathrm{signShift}(a_1+\mathrm{par}(w))+\mathrm{signShift}(a_2+\mathrm{par}(w))$ as complex numbers, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$, and whenever `archR' w hw` $=\mathrm{discrete}\,u_0\,n$ one has $k(w)=n+1$.
--
--   Fifthly, the Whittaker coefficients of $\varphi$ factorise: for every unit idele $a$ and every $g$ in `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection of $GL_2(\mathbb{A}_{\mathbb{Q}})$), the first Whittaker coefficient of $\varphi$ with respect to `psiQ` at $\mathrm{diag}(a,1)\cdot g$ equals $\bigl(\prod_{w\ \mathrm{infinite}} W_r(w)(\iota_w(a_\infty(w)))\bigr)\cdot C(a_{\mathrm{fin}},g)$, where $a_\infty$ and $a_{\mathrm{fin}}$ are the infinite and finite components of $a$ and $\iota_w$ is the embedding of the completion at $w$ into $\mathbb{C}$.
--
--   Sixthly, the archimedean factors $W_r$ obey the following clauses. If `archR' w hw` is principal with both parities equal to $a_1$ and $\mathrm{par}(w)=a_1$, then $W_r(w)(-t)=(-1)^{a_1}W_r(w)(t)$ for all real $t$. If `archR' w hw` $=\mathrm{discrete}\,u_0\,n$, then $W_r(w)(t)=0$ for all $t<0$. If `archR' w hw` is principal with both parities equal to $a_1$ and $\mathrm{par}(w)=a_1+1$, then there is $s_0\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(w)(t)+(-1)^{a_1}W_r(w)(-t))/t$ converges at $s$ and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor at $s$ of (`archR' w hw`)`.twist 0 a₁`, the parameter obtained by adding $a_1$ to both parities and leaving the exponents unchanged. Finally, for every real $w$ and every $b\in\mathbb{Z}/2$ with $b=\mathrm{par}(w)$ or $b=\mathrm{par}(w)+$ (`archR' w hw`)`.centralSign`, there is $s_0\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(w)(t)+(-1)^{b}W_r(w)(-t))/t$ converges at $s$ and equals the archimedean factor at $s$ of (`archR' w hw`)`.twist 0 b`, that is $\Gamma_{\mathbb{R}}(s+u_1+\mathrm{signShift}(a_1+b))\,\Gamma_{\mathbb{R}}(s+u_2+\mathrm{signShift}(a_2+b))$ in the principal case and $\Gamma_{\mathbb{C}}(s+u_0+n/2)$ in the discrete case.
--
--   Since `_hne₂` forces every `archR w hw` to be principal with distinct parities, and clause (i) preserves that, the clauses above conditioned on a principal parameter with two equal parities, and those conditioned on a discrete parameter, are vacuous under these hypotheses; they are part of the shape of the conclusion.
--
--   This is the archimedean-analytic input to the converse theorem in the Langlands–Tunnell argument over $\mathbb{Q}$: starting from a single weight-one cusp form in a cuspidal constituent whose local Whittaker spaces are irreducible, admissible and smooth, it produces, for each choice of parity twist, a cusp form with the same Hecke eigensystem whose Whittaker coefficients split as an archimedean product times a finite-adelic factor $C$ with $C(1,1)\neq 0$, with prescribed gamma-factor Mellin transforms at the real place. It is used by [`LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization`](thm.html#LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization), which removes the hypotheses on the archimedean parameter by constructing it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne.lean

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

theorem LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
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
