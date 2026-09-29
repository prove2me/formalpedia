-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight
-- name    : LanglandsTunnell.exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d5de4096-ed60-56e9-91a9-393a43251784
-- title:
--   Whittaker factorisation of a minimal-weight Casimir eigenvector over ℚ
-- statement:
--   The setting is $\mathrm{GL}_2$ over $\mathbb{Q}$. Fix real numbers $c,u,d_1,d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and write $D=\bigcup_{x\in T}\{s\cdot x: s\in \mathtt{centreCutSiegelSet}\,\mathbb{Q}\,c\,u\,d_1\,d_2\}$ for the corresponding finite union of right translates of the centre-cut Siegel set, the latter consisting of those $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose window quantity `xWindowSq` at every infinite place is at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. All automorphic data are taken at the carrier `productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`: the adelic Haar measure and Borel structure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the fundamental region $D$, the full centre subgroup $Z=\top$, level subgroups $N\mapsto \mathtt{levelOne}(N)\cap\ker(\text{archimedean projection})$, Hecke generators $v\mapsto \mathtt{heckeGen}\,v$, and the Haar measure on $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box.
--
--   The hypotheses on this carrier are `_hd`, that $d_1<d_2$, and `_hcov`, that $D$ covers modulo the centre: for every $g\in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ there are $\gamma\in \mathrm{GL}_2(\mathbb{Q})$ and $z\in \mathbb{A}_{\mathbb{Q}}^{\times}$ with $\gamma g\,z\in D$.
--
--   Further data: a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex eigenvalues $\Phi.a$, $\Phi.b$ and level $\Phi.\mathrm{level}$; a smooth cusp realisation $R$ at the above carrier for the rescaled eigensystem $\Phi.\mathtt{toRawCentral}$ (same level and same $\Phi.a$, with $b$ replaced by $v\mapsto (\#\mathcal{O}/v)^{-1}\Phi.b(v)$), with `_hR` requiring $R.\mathtt{toFun}$ to be continuous; an additive character $\psi$ of $\mathbb{A}_{\mathbb{Q}}$ with `_hψ` asserting that $\psi$ is a global additive character (trivial on $\mathbb{Q}$, continuous, nontrivial) and `_hψr` that at every real place $w$ and every infinite adele $x$ supported at $w$ one has $\psi(x,0)=\exp(2\pi i\, \iota_w(x_w))$, $\iota_w$ the embedding of $w$'s completion into $\mathbb{C}$; a finite set $S$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$ with `_hS` requiring $R.\mathtt{exceptionalSet}\subseteq S$; and a family $\mathtt{archR}$ assigning to each real place $w$ a real archimedean parameter, either $\mathtt{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathtt{discrete}(u_0,n)$ with $n\ge 1$. Two hypotheses constrain these parameters: `_htype`, that $|\mathrm{Re}(u_1-u_2)|<1$ for every principal parameter, and `_hcen`, that for every real $w$ the archimedean component at $w$ of the central character $R.\mathtt{centralChar}$ (transported along the isomorphism of the full subgroup with $\mathbb{A}_{\mathbb{Q}}^{\times}$) is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,(\text{centralExponent}+1)}\,(\iota_w(x)/\|x\|)^{\text{centralSign}}$, with the central exponent and central sign of $\mathtt{archR}\,w$.
--
--   Finally a function $\varphi_1:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ and weights $k_1:\{\text{infinite places}\}\to\mathbb{Z}$ subject to: `_hiso`, that $\varphi_1$ is an isotypic cusp form at the carrier for the central character $R.\mathtt{centralChar}$, level $\Phi.\mathrm{level}$, exceptional set $S$ and eigensystem $\Phi$ (that is: smooth cuspidal automorphic and $K_f$-smooth, continuous, invariant under right translation by the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ for $v\notin S$, and satisfying $\varphi_1(\mathtt{centralScalar}(\det \mathtt{heckeGen}\,v)\,g)=(\#\mathcal{O}/v)^{-1}\Phi.b(v)\varphi_1(g)$ for $v\notin S$); `_hne`, that $\varphi_1\neq 0$; `_hconv`, that $\varphi_1$ is reproduced by right convolution, $\mathtt{rightConv}\,\varphi_1\,\alpha=\varphi_1$ for some factorizable test function $\alpha$ (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor); `_hwt`, that at every real place $w$ the function $\varphi_1$ has archimedean character $\mathtt{archWeightCharAt}\,hw\,(k_1 w)$, the $(k_1w)$-th power of the basic weight character on $\mathtt{rowIsometrySubgroup}_0$ of $w$'s completion, in the sense of the predicate `HasArchCharacterAt₀`; `_hminp`, the minimality condition at principal parameters, $k_1w\in\{0,1\}$ and $k_1w\equiv a_1+a_2 \pmod 2$; `_hmind`, that $k_1w=n+1$ at a discrete parameter $\mathtt{discrete}(u_0,n)$; `_hpair`, that at every real place $\varphi_1$ is archimedean-smooth and an eigenfunction of the Casimir operator $\mathtt{archCasimirAt}=-\bigl(\tfrac14 H^2-\tfrac12 H+E\,F^-\bigr)$ (formed from the right-translation derivatives along the flows $H$, $E$, $F^-$ at $w$) with eigenvalue the Laplace eigenvalue of $\mathtt{archR}\,w$, namely $\tfrac14-((u_1-u_2)/2)^2$ in the principal case and $(1-n^2)/4$ in the discrete case; `_hJ`, that for a principal parameter with $a_1=a_2$ one has $\varphi_1(g\cdot J_w)=(-1)^{a_1}\varphi_1(g)$ for all $g$, with $J$ the standard reflection at $w$; `_hlow`, that at a discrete parameter the lowering combination $D_H\varphi_1-i(D_E\varphi_1+D_{F^-}\varphi_1)$ vanishes; `_hlow1`, the same vanishing at a principal parameter whose two complex components coincide and whose two signs differ; and `_heq`, that every principal parameter has $a_1=a_2$ or $u_1=u_2$.
--
--   The conclusion asserts the existence of a single function $C:\mathbb{A}_{\mathbb{Q},f}\to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ with the following two properties.
--
--   First, there is a family of archimedean profiles $W^{(1)}:\{\text{infinite places}\}\to(\mathbb{C}\to\mathbb{C})$ such that for every $a\in\mathbb{A}_{\mathbb{Q}}^{\times}$ and every $g$ in the kernel of the archimedean projection,
--   $$\mathtt{whittakerCoefficient}\,\psi\,\varphi_1\,1\,(\mathtt{diagOne}(a)\,g)=\Bigl(\prod_w W^{(1)}_w\bigl(\iota_w(a_\infty(w))\bigr)\Bigr)\,C(a_f,g),$$
--   the Whittaker coefficient being $\int \varphi_1(\mathtt{unipotentGL2}(x)\,h)\,\psi(-x)\,d\nu(x)$ with $\nu$ the box-conditioned Haar measure of the carrier.
--
--   Secondly, for every parity assignment $\mathtt{par}$ from infinite places to $\mathbb{Z}/2$ there exist a function $\varphi$, archimedean profiles $W$ and weights $k$ such that all of the following hold. (i) Either $\varphi=\varphi_1$, or there are a real place $w$ and a constant $c_r\in\mathbb{C}$ with $\varphi=c_r\bigl(D_H\varphi_1+i(D_E\varphi_1+D_{F^-}\varphi_1)\bigr)$, the raising combination at $w$. (ii) $\varphi$ is an isotypic cusp form at the carrier for $R.\mathtt{centralChar}$, level $\Phi.\mathrm{level}$, exceptional set $S$ and eigensystem $\Phi$. (iii) $\varphi\neq 0$. (iv) $\mathtt{rightConv}\,\varphi\,\alpha=\varphi$ for some factorizable test function $\alpha$. (v) At every real place $w$, $\varphi$ has archimedean character $\mathtt{archWeightCharAt}\,hw\,(k w)$. (vi) At a principal parameter $\mathtt{principal}(u_1,a_1,u_2,a_2)$ at $w$, $(k w)=\mathtt{signShift}(a_1+\mathtt{par}\,w)+\mathtt{signShift}(a_2+\mathtt{par}\,w)$ as a complex number, where $\mathtt{signShift}(0)=0$ and $\mathtt{signShift}(1)=1$. (vii) At a discrete parameter $\mathtt{discrete}(u_0,n)$ at $w$, $k w=n+1$. (viii) For every $a\in\mathbb{A}_{\mathbb{Q}}^{\times}$ and every $g$ in the kernel of the archimedean projection, the Whittaker coefficient of $\varphi$ at $\mathtt{diagOne}(a)\,g$ equals $\bigl(\prod_w W_w(\iota_w(a_\infty(w)))\bigr)\,C(a_f,g)$, with the same $C$ as in the first property. (ix) At a principal parameter with equal signs $a_1$ in both slots and $\mathtt{par}\,w=a_1$, the profile satisfies $W_w(-t)=(-1)^{a_1}W_w(t)$ for all real $t$. (x) At a discrete parameter at $w$, $W_w(t)=0$ for all real $t<0$. (xi) At a principal parameter with equal signs $a_1$ and $\mathtt{par}\,w=a_1+1$, there is $s_0\in\mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s>s_0$ the Mellin integral of $t\mapsto (W_w(t)+(-1)^{a_1}W_w(-t))/t$ converges at $s$ and
--   $$\int_0^\infty \frac{W_w(t)+(-1)^{a_1}W_w(-t)}{t}\,t^{s}\frac{dt}{t}=\frac{2s+u_1+u_2-1}{4\pi}\cdot \mathtt{archFactor}\bigl((\mathtt{archR}\,w)\mathtt{.twist}\,0\,a_1\bigr)(s).$$
--   (xii) For every real place $w$ and every $b\in\mathbb{Z}/2$ with $b=\mathtt{par}\,w$ or $b=\mathtt{par}\,w+\mathtt{centralSign}(\mathtt{archR}\,w)$, there is $s_0\in\mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s>s_0$ the Mellin integral of $t\mapsto (W_w(t)+(-1)^{b}W_w(-t))/t$ converges at $s$ and equals $\mathtt{archFactor}\bigl((\mathtt{archR}\,w)\mathtt{.twist}\,0\,b\bigr)(s)$. Here the twist by $(0,b)$ shifts both signs of a principal parameter by $b$ and leaves a discrete parameter unchanged, and its archimedean factor is $\Gamma_{\mathbb{R}}(s+u_1+\mathtt{signShift}(a_1+b))\Gamma_{\mathbb{R}}(s+u_2+\mathtt{signShift}(a_2+b))$ in the principal case and $\Gamma_{\mathbb{C}}(s+u_0+n/2)$ in the discrete case.
--
--   This is the archimedean input to the converse theorem in the Langlands–Tunnell step: starting from a single nonzero minimal-weight Casimir eigenvector $\varphi_1$ in the $\Phi$-isotypic cuspidal space, it produces, for each parity assignment, a vector of the weight family (either $\varphi_1$ itself or its image under the raising operator at a real place) whose Whittaker coefficient factorises as an archimedean profile times one finite factor $C$ shared by the whole family, with the prescribed Mellin transforms given by the gamma factors of the twisted archimedean parameter. It is used by [`LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight`](thm.html#LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight), where the shared finite factor is normalised at a reference point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
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

theorem LanglandsTunnell.exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
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
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,

    (∃ Wr₁ : InfinitePlace ℚ → ℂ → ℂ,
      ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                  (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                  (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            ψ φ₁ 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr₁ w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),

        (φ = φ₁ ∨ ∃ (w : InfinitePlace ℚ) (hw : w.IsReal) (cr : ℂ),
          φ = cr • (archDerivAt hw ArchDir.H φ₁
            + Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁))) ∧
        IsIsotypicCuspFormAt ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
              (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
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
                (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                  (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                  (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                ψ φ 1 (diagOne a * g)
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
