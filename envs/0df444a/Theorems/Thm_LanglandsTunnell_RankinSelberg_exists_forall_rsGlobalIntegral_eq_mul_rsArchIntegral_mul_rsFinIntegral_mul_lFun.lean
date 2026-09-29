-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/517907af-c7a9-558c-8b38-2c6a18c65c70
-- title:
--   Rankin–Selberg integral as archimedean times finite integral times partial L-function
-- statement:
--   Fixed data. A number field $K$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral; a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex values, that is, a nonzero level ideal of $\mathcal{O}_{\mathbb{Q}}$ together with two families $\Phi.a,\Phi.b$ of complex numbers indexed by the primes of $\mathcal{O}_{\mathbb{Q}}$; a finite set $SQ$ of primes of $\mathcal{O}_{\mathbb{Q}}$; a real archimedean parameter $P$ (either of principal type, given by $(u_1,a_1,u_2,a_2)$ with $a_i\in\mathbb{Z}/2$, or of discrete type, given by $(u,k)$ with $k\ge 1$); a group homomorphism $\mu$ from the idèle group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$; and twisting data at the infinite places of $K$: complex numbers $uR_w$ and classes $aR_w\in\mathbb{Z}/2$ for the real places $w$, complex numbers $uC_w$ and integers $kC_w$ for the complex places. The hypothesis `_hunr` requires that no prime $p\notin SQ$ satisfies `IsRamifiedIn K p`, i.e. that every prime $\mathfrak{P}$ of $\mathcal{O}_K$ in the fibre over such a $p$ has ramification index $1$. Standing assumptions are that $GL_2(\mathbb{A}_{\mathbb{Q}})$ is second countable and that the residue rings $\mathcal{O}_{\mathbb{Q}}/p$ are finite, and the Borel $\sigma$-algebra with its Haar measure is used on $GL_2(\mathbb{A}_{\mathbb{Q}})$.
--
--   Further fixed data: a subset $Dm$ of $GL_2(\mathbb{A}_{\mathbb{Q}})$ and a complex constant $c$; an additive character $\psi$ of $\mathbb{A}_{\mathbb{Q}}$ with $\psi^{-1}$ equal to the standard character `psiQ` of $\mathbb{Q}$ (hypothesis `hψQ`); a Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection of $GL_2(\mathbb{A}_{\mathbb{Q}})$, and a Haar measure $\mu_{N,f}$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the unipotent subgroup $\{\,(\begin{smallmatrix}1&x\\0&1\end{smallmatrix})\,\}$ of $GL_2(\mathbb{A}_{\mathbb{Q}})$ intersected with that finite-adelic subgroup; and a family $\varpi_p$ of elements of the valuation rings $\mathcal{O}_{\mathbb{Q},p}$ such that for $p\notin SQ$ the image of $\varpi_p$ in the completion is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), so is a uniformiser there. Finally, a natural number $n$, functions $\varphi_i$ on $GL_2(\mathbb{A}_{\mathbb{Q}})$ and functions $\Theta_i, W_i$ on $GL_3(\mathbb{A}_{\mathbb{Q}})$, for $i\in\{0,\dots,n-1\}$, all complex valued.
--
--   The assertion is universally quantified over the following additional objects and hypotheses, $GL_2(\mathbb{R})$ carrying its Borel $\sigma$-algebra.
--
--   Measures and their splitting. A Haar measure $\mu_{N,\infty}$ on the unipotent subgroup `realUnipotent` of $GL_2(\mathbb{R})$; the hypothesis `_hsplit` that the image of the adelic Haar measure `adelicGLHaar` on $GL_2(\mathbb{A}_{\mathbb{Q}})$ under $g\mapsto(\mathtt{ratArchGL2}\,g,\ \mathtt{RSCarrier.finFactor}\,g)$ — the archimedean component of $g$ viewed in $GL_2(\mathbb{R})$, and the finite-adelic part $(\mathtt{archRealGLAt}\,(\mathtt{ratArchGL2}\,g))^{-1}g$ — is the product of [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) (Lebesgue measure on $2\times 2$ real matrices pulled back to $GL_2(\mathbb{R})$ and given the density $|\det g|^{-2}$) with $\mu_f$; and the hypothesis `_hNsplit` that the image of `unipotentHaar ℚ` (the additive adelic Haar measure normalised by the volume of `adelicBox`, transported to the adelic unipotent subgroup) under the same pair of maps is the product of the pushforwards of $\mu_{N,\infty}$ and $\mu_{N,f}$ along the inclusions.
--
--   The Rankin–Selberg datum. Write $c_\mu(\mathfrak{P})$ for $\mu$ evaluated at the uniformiser idèle `uniformizerIdele K 𝔓` when $\mu$ is unramified at $\mathfrak{P}$ in the sense of `IsUnramifiedCharAt` (the local component of $\mu$ is trivial on the units of the valuation ring), and $c_\mu(\mathfrak{P})=0$ otherwise. Let $D$ denote `rsDatum ℚ SQ Φ.a Φ.b` $c_\mu$ together with four gamma multisets: `twistedGammaR` of the constant family $P$ twisted by $(uR_w,aR_w)$, summed over the real places of $K$; `twistedGammaC`, the sum over real places of the `gammaC` multiset of the same twists plus the sum over complex places of the `gammaC` multiset of the base change $P.\mathrm{baseChange}$ twisted by $(uC_w,kC_w)$; and the two dual multisets, formed in the same way from the dual parameters (the duals of $P$ and of $P.\mathrm{baseChange}$, which negate the $u$-entries) with $uR_w$, $uC_w$, $kC_w$ replaced by their negatives and $aR_w$ unchanged. Thus $D$ is the $L$-datum indexed by the primes $p\notin SQ$, with norm $|\mathcal{O}_{\mathbb{Q}}/p|$, Euler factor `rsEulerPoly` formed from $\Phi.a(p)$, $\Phi.b(p)$ and the three induced coefficients $E_1,E_2,E_3$ of $c_\mu$ at $p$ (the signed coefficients of degrees $1,2,3$ of `inducedEulerPoly`), dual factor formed likewise from $\Phi.a(p)/\Phi.b(p)$, $\Phi.b(p)^{-1}$ and the induced coefficients of $\mathfrak{P}\mapsto c_\mu(\mathfrak{P})^{-1}$, abscissa $1$, centre $1/2$ and degree $6$. The hypothesis `_hconv` is that $D$ converges: for every $s$ with $\operatorname{Re} s>1$ the families $\|\mathrm{euler}_p(N_p^{-s})-1\|$ and $\|\mathrm{dual}_p(N_p^{-s})-1\|$ are summable and both $D.\mathrm{LFun}(s)$ and $D.\mathrm{LFunDual}(s)$ are nonzero. The hypothesis `_hwf` is that $D$ is well formed: all norms are at least $2$, all Euler and dual polynomials have constant term $1$ and degree at most $6$, and every entry $\nu$ of the four gamma multisets satisfies $-\operatorname{Re}\nu\le 1$.
--
--   Factorisation of the Whittaker coefficients. Functions $WA_i$ on $GL_2(\mathbb{R})$ and $Wf_i$ on the finite-adelic subgroup, subject to `_hWAf`: for every $i$ and every $g$, the Whittaker coefficient at $\alpha=1$ of $\varphi_i$ for the standard character `psiQ`, taken with respect to the carrier pins `productionPinsOf` built from the domain `classRepSiegelSet ℚ (1/2) 1 (1/2) 2`, the level subgroups $N\mapsto \mathtt{levelOne}\,N\sqcap\mathtt{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen`, and the adelic additive Haar measure conditioned on `adelicBox ℚ`, namely $\int \varphi_i(u(x)g)\,\psi_{\mathbb{Q}}(-x)\,dx$, equals $WA_i(\mathtt{ratArchGL2}\,g)\cdot Wf_i(\mathtt{finFactor}\,g)$.
--
--   Local properties of $Wf_i$ (hypothesis `_hHL`, four clauses for each $i$, all for primes $p\notin SQ$): $Wf_i\circ\mathtt{finFactor}$ transforms on the left under the unipotent element $u(x)$ embedded at $p$ by the local character `psiLoc psiQ p` at $x$; it is invariant under right multiplication by elements of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) embedded at $p$ (the preimage under the local embedding of the finite level-one subgroup at the unit ideal); the Hecke relation holds, namely the sum over the residue classes $r$ of $\mathcal{O}_{\mathbb{Q}}/p$ of the values at $g\cdot\bigl(\begin{smallmatrix}\varpi_p&\beta_r\\0&1\end{smallmatrix}\bigr)$, with $\beta_r$ the chosen lift of $r$, plus the value at $g\cdot\bigl(\begin{smallmatrix}1&0\\0&\varpi_p\end{smallmatrix}\bigr)$, equals $\Phi.a(p)$ times the value at $g$; and right translation by the scalar matrix $\varpi_p I$ at $p$ multiplies the value by $\Phi.b(p)/|\mathcal{O}_{\mathbb{Q}}/p|$.
--
--   Factorisation of $W_i$ on the embedded $GL_2$. Functions $FA_i$ on $GL_2(\mathbb{R})$ and $Ff_i$ on the finite-adelic subgroup with `_hFAf`: $W_i(\iota(g))=FA_i(\mathtt{ratArchGL2}\,g)\cdot Ff_i(\mathtt{finFactor}\,g)$ for all $g$, where $\iota$ is the embedding of $GL_2$ into $GL_3$.
--
--   Recursive coefficient tables. A table $hH$ with `_hHrec`: $hH(p,0)=1$, $hH(p,1)=E_1(p)$, $hH(p,2)=E_1(p)^2-E_2(p)$, and $hH(p,m+3)=E_1(p)hH(p,m+2)-E_2(p)hH(p,m+1)+E_3(p)hH(p,m)$, the $E_j$ being the induced coefficients of $c_\mu$ as above. A table $uH$ with `_uHrec`: $uH(p,k,0)=hH(p,k)$ and $uH(p,k_1,k_2+1)=hH(p,k_1)hH(p,k_2+1)-hH(p,k_1+1)hH(p,k_2)$. A table $uZ$ on pairs of integers with `_uZrec`: $uZ(p,m_1,m_2)=0$ whenever $m_2<0$ or $m_1<m_2$, and $uZ(p,k_1,k_2)=uH(p,k_1,k_2)$ for natural numbers $k_2\le k_1$.
--
--   Local properties of $Ff_i$ (hypothesis `_hTT`, two clauses for each $i$, for primes $p\notin SQ$): $Ff_i\circ\mathtt{finFactor}$ is invariant under right multiplication by `localLevelOne p ⊤` embedded at $p$; and for $g$ whose component at $p$ is trivial and for all integers $m_1,m_2$, right translation by $\mathrm{diag}(\varpi_p^{m_1-m_2},1)\cdot(\varpi_pI)^{m_2}$ at $p$ multiplies the value at $g$ by $|\mathcal{O}_{\mathbb{Q}}/p|^{-m_1}\,uZ(p,m_1,m_2)$.
--
--   The unfolded integrand. Functions $f_i(s',\cdot)$ with `_hf`: $f_i(s',g)$ is the Whittaker coefficient at $\alpha=1$ of $\varphi_i$ for the character $\psi^{-1}$ with the same carrier pins, times $W_i(\iota(g))$, times $\|\det g\|_{\mathbb{A}}^{\,s'-1/2}$, where $\|\cdot\|_{\mathbb{A}}$ is the idèle norm. The hypothesis `_hJ3f` states that for each $i$ there is $\sigma_0$ such that for $\operatorname{Re} s'>\sigma_0$ the global integral $\int_{Dm}\varphi_i(g)\Theta_i(\iota(g))\|\det g\|^{s'-1/2}\,dg$ equals $c$ times the integral of $f_i(s',\cdot)$ over the quotient `UnipotentQuotient ℚ`, evaluated along chosen representatives, against `unipotentQuotientMeasure ℚ`. The hypothesis `_hfm` states that each $f_i(s',\cdot)$ is measurable, `_hfN` that it is left invariant under the adelic unipotent subgroup, and `_hint7` that for each $i$ there is $\sigma_7$ such that for $\operatorname{Re} s'>\sigma_7$ the induced function on the quotient is integrable.
--
--   Conclusion. For every $i$ there exists $\sigma\in\mathbb{R}$ such that for all $s\in\mathbb{C}$ with $\sigma<\operatorname{Re} s$,
--   $$\mathtt{rsGlobalIntegral}\ Dm\ (s-\tfrac12)\ \varphi_i\ \Theta_i\ =\ c\cdot \mathtt{rsArchIntegral}\ \mathtt{archMeasure}\ \mu_{N,\infty}\ (s-\tfrac12)\ WA_i\ FA_i\ \cdot\ \mathtt{rsFinIntegral}\ \mu_f\ \mu_{N,f}\ (s-\tfrac12)\ \tilde W_i\ \tilde F_i\ \cdot\ D.\mathrm{LFun}(s),$$
--   where: the left-hand side is $\int_{Dm}\varphi_i(g)\Theta_i(\iota(g))\,\|\det g\|^{(s-1/2)-1/2}\,dg$ against the adelic Haar measure; `rsArchIntegral` is the local Rankin–Selberg integral `rsLocalIntegral` for `archMeasure`, the unipotent subgroup of $GL_2(\mathbb{R})$ with Haar measure $\mu_{N,\infty}$ and modulus $g\mapsto|\det g|$, at the parameter $s-1/2$ and the pair $(WA_i,FA_i)$; `rsFinIntegral` is the corresponding local integral for $\mu_f$, the finite unipotent subgroup with Haar measure $\mu_{N,f}$ and modulus the idèle norm of the determinant, at $s-1/2$; $\tilde W_i$ and $\tilde F_i$ are the indicator-truncations of $g\mapsto Wf_i(\mathtt{finFactor}\,g)$ and $g\mapsto Ff_i(\mathtt{finFactor}\,g)$ by the set of those $g$ in the finite-adelic subgroup whose component at every prime $p\notin SQ$ can be written as a product $n\,k$ with $n$ in the image of `unipotentGL2Hom` over the completion at $p$ and $k\in\mathtt{localLevelOne}\ p\ \top$; and $D.\mathrm{LFun}(s)=\prod_{p\notin SQ}\bigl(\mathrm{euler}_p(N_p^{-s})\bigr)^{-1}$ is the partial $L$-function of the Rankin–Selberg datum $D$ described above. Note the shift: the global and local integrals are taken at $s-1/2$, while the $L$-function is evaluated at $s$.
--
--   This is the unfolding step of the $GL_2\times GL_3$ Rankin–Selberg method used in the Langlands–Tunnell part of the argument: granted a product decomposition of the Whittaker coefficient and of the $GL_3$ test function into archimedean and finite parts, together with the local Hecke and invariance relations at the primes outside $SQ$, the global zeta integral of the pair $(\varphi_i,\Theta_i)$ splits as a constant times an archimedean local integral, a finite local integral cut down to the cells $N(\mathbb{Q}_p)K_p$ off $SQ$, and the partial $L$-function attached to the Rankin–Selberg $L$-datum built from $\Phi$, the character $\mu$ of the idèles of $K$ and the archimedean parameter $P$. It feeds the statements producing an entire, strip-bounded continuation of the $L$-function of that datum and the nonvanishing reference form of the factorisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
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

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse
open scoped Classical in

theorem
LanglandsTunnell.RankinSelberg.exists_forall_rsGlobalIntegral_eq_mul_rsArchIntegral_mul_rsFinIntegral_mul_lFun
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (P : RealArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (_hunr : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ¬ IsRamifiedIn K p)
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (Dm : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (c : ℂ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (φ : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ W : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μNArch : MeasureTheory.Measure RSCarrier.realUnipotent) [μNArch.IsHaarMeasure]
      (_hsplit : MeasureTheory.Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, RSCarrier.finFactor g))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = RSCarrier.archMeasure.prod μf)
      (_hNsplit : MeasureTheory.Measure.map
        (fun n : adelicUnipotent ℚ => (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (MeasureTheory.Measure.map Subtype.val μNArch).prod (MeasureTheory.Measure.map Subtype.val μNFin))
      (_hconv : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).Converges)
      (_hwf : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).WellFormed)

      (WA : Fin n → GL (Fin 2) ℝ → ℂ) (Wf : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hWAf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ
            N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                NumberField.StandardAddChar.psiQ (φ i) 1 g =
          WA i (ratArchGL2 g) * Wf i (RSCarrier.finFactor g))

      (_hHL : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf i (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ p x * Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            Φ.a p * Wf i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf i (RSCarrier.finFactor g)))
      (FA : Fin n → GL (Fin 2) ℝ → ℂ) (Ff : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hFAf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ), W i (iota (𝓞 ℚ) ℚ g) = FA i (ratArchGL2 g) * Ff i
          (RSCarrier.finFactor g))

      (hH : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ)
      (_hHrec : (∀ p, hH p 0 = 1) ∧ (∀ p, hH p 1 = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ
          (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p) ∧
        (∀ p, hH p 2 = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else
            0) p ^ 2 - inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else
                0) p) ∧
        (∀ p (n : ℕ), hH p (n + 3) = inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) :
            ℂˣ) : ℂ) else 0) p * hH p (n + 2) - inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ
                (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p * hH p (n + 1) +
          inducedE3 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p * hH p
              n))
      (uH : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℕ → ℂ)
      (_uHrec : (∀ p k, uH p k 0 = hH p k) ∧
        (∀ p k₁ k₂, uH p k₁ (k₂ + 1) = hH p k₁ * hH p (k₂ + 1) - hH p (k₁ + 1) * hH p k₂))
      (uZ : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℤ → ℂ)
      (_uZrec : (∀ p (m₁ m₂ : ℤ), (m₂ < 0 ∨ m₁ < m₂) → uZ p m₁ m₂ = 0) ∧
        (∀ p (k₁ k₂ : ℕ), k₂ ≤ k₁ → uZ p k₁ k₂ = uH p k₁ k₂))
      (_hTT : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Ff i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Ff i (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ),
          localAt ℚ p g = 1 →
            Ff i (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p
                (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p
                    hp) (m₁ - m₂) *
                  UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ
                      p hp) ^ m₂))) =
              Ff i (RSCarrier.finFactor g) * ((Ideal.absNorm p.asIdeal : ℂ)⁻¹ ^ m₁ * uZ p m₁ m₂)))

      (f : Fin n → ℂ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hf : ∀ i s' g, f i s' g =
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ
            N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (φ i) 1 g * W i
                (iota (𝓞 ℚ) ℚ g) *
          ((detNorm g : ℝ) : ℂ) ^ (s' - 1 / 2))
      (_hJ3f : ∀ i, ∃ σ0 : ℝ, ∀ s' : ℂ, σ0 < s'.re →
        rsGlobalIntegral Dm s' (φ i) (Θ i) = c * ∫ q, f i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ))

      (_hfm : ∀ (i : Fin n) (s' : ℂ), Measurable (f i s'))
      (_hfN : ∀ (i : Fin n) (s' : ℂ) (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        f i s' ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f i s' g)
      (_hint7 : ∀ i : Fin n, ∃ σ7 : ℝ, ∀ s' : ℂ, σ7 < s'.re →
        MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f i s' (Quotient.out q)) (unipotentQuotientMeasure
            ℚ)),
    ∀ i : Fin n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i) =
        c * RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WA i) (FA i) *
        RSCarrier.rsFinIntegral μf μNFin (s - 1 / 2)
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf i (RSCarrier.finFactor (g :
                      AdelicGL2 (𝓞 ℚ) ℚ))))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Ff i (RSCarrier.finFactor (g :
                      AdelicGL2 (𝓞 ℚ) ℚ)))) *
        (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFun s := by sorry
