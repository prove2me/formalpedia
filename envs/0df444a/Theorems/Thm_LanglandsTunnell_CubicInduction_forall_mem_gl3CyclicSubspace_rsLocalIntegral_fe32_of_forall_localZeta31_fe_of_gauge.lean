-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/59701a11-cdd1-5d8b-8aae-35802c3f1ed7
-- title:
--   Local GL₃timesGL₂ functional equation on the cyclic space
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $\mathbb{Q}_v$ for the completion $v.\mathtt{adicCompletion}\ \mathbb{Q}$, $|\cdot|_v$ for the normalised module `TateLocal.modulus`, and $\mathbf{N}v$ for the absolute norm of the prime ideal of $v$. Let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$, assumed (hypothesis `hψinv`) to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), and let $W\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function subject to the following groups of hypotheses.
--
--   *Whittaker transformation law* (`hW`): $W(u(x,y,z)\,g)=\psi_v(x+y)\,W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)=\begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$.
--
--   *Multiplicity one* (`hmult`): the space of $\psi_v$-Whittaker functionals on the representation `gl3CyclicRep W` of $\mathrm{GL}_3(\mathbb{Q}_v)$ on $\langle W\rangle:=$ `gl3CyclicSubspace W`, the $\mathbb{C}$-span of the right translates $h\mapsto W(hg)$, has rank at most $1$.
--
--   *Regeneration* (`hirr`): every non-zero $F\in\langle W\rangle$ satisfies $W\in\langle F\rangle$.
--
--   *Smoothness* (`hsm`): some open subgroup $U_v\le \mathrm{GL}_3(\mathbb{Q}_v)$ fixes $W$ under right translation.
--
--   *Admissibility* (`hadm`): for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $U_v$-right-invariant member of $\langle W\rangle$ lies in the $\mathbb{C}$-span of $B$.
--
--   *Gauge estimate* (`hWgauge`): there are $B,C\in\mathbb{R}$ and $t\in\mathbb{N}$ such that, writing $X(h)=\mathtt{detSize}(h)\cdot\mathtt{lastRowSup}(h)/\mathtt{minorSup}(h)^2$ and $Y(h)=\mathtt{minorSup}(h)/\mathtt{lastRowSup}(h)^2$ — with $\mathtt{detSize}(h)=\|\det h\|$, $\mathtt{lastRowSup}(h)$ the maximum of the norms of the three entries of the last row of $h$, and $\mathtt{minorSup}(h)$ the maximum of the norms of the three $2\times 2$ minors formed from rows $1$ and $2$ — one has $W(h)=0$ whenever the conjunction $X(h)\le B$ and $Y(h)\le B$ fails, and $\|W(h)\|\le C/(X(h)\,Y(h))^{t}$ whenever it holds.
--
--   *Central character* (`ωv`, `hωu`, `hω`): a homomorphism $\omega_v\colon \mathbb{Q}_v^\times\to\mathbb{C}^\times$ with $\|\omega_v(z)\|=1$ for all $z$, such that $W(\mathrm{scalar}(t)\,h)=\omega_v(t)\,W(h)$ for all $t\in\mathbb{Q}_v^\times$ and $h\in\mathrm{GL}_3(\mathbb{Q}_v)$.
--
--   *Uniformiser* (`hπ`, `hϖ`): an element $\varpi$ of the valuation ring whose image in $\mathbb{Q}_v$ is non-zero and has valuation $\exp(-1)$.
--
--   *Euler-factor functional equation for the $(3,1)$ zeta integrals* (`h31`), in terms of polynomials $E,E^{\vee}\in\mathbb{C}[T]$, a constant $\varepsilon\in\mathbb{C}$ and an exponent $\ell\in\mathbb{N}$: for every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ there exist $P\colon\mathbb{C}\to\mathbb{C}$ and $\sigma_0,\sigma_1\in\mathbb{R}$ such that (i) $P$ is rational in $\mathbf{N}v^{-s}$ up to a monomial, that is, there are polynomials $Q,R$ with $R\neq 0$ and an $m\in\mathbb{N}$ with $P(s)\,R(\mathbf{N}v^{-s})=Q(\mathbf{N}v^{-s})\,\mathbf{N}v^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` holds at $g$ above $\sigma_0$, i.e. for $\mathrm{Re}\,s>\sigma_0$ the function $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|_v^{\,s-1}$ is integrable for the measure $\mu^{\times}$ obtained by pulling back along $a\mapsto a$ the multiplicative measure `mulMeasure` of the self-dual additive Haar measure `selfDualHaarAt ℚ v`; (iii) for $\mathrm{Re}\,s>\sigma_0$, $\mathtt{localZeta30}(s,g)=E(\mathbf{N}v^{-s})^{-1}P(s)$, the zeta integral being taken with trivial character; (iv) `IsLocalZeta31ConvergentAbove` holds for $\mathtt{dualWhittakerFn3}\,W$, i.e. $h\mapsto W(w_3\,{}^{t}h^{-1})$ with $w_3$ the antidiagonal permutation matrix `longWeyl3`, at the point $w'_3\,{}^{t}g^{-1}$ (with $w'_3$ the transposition of the last two coordinates) above $\sigma_1$, for $\mu^{\times}$ times `selfDualHaarAt ℚ v`; and (v) for $\mathrm{Re}(1-s)>\sigma_1$, $\mathtt{localZetaDual31}(1-s,g)=E^{\vee}(\mathbf{N}v^{-(1-s)})^{-1}\bigl(\varepsilon\,\mathbf{N}v^{\ell(1/2-s)}P(s)\bigr)$, where `localZetaDual31` is by definition the $(3,1)$ integral of $\mathtt{dualWhittakerFn3}\,W$ with inverted character at $w'_3\,{}^{t}g^{-1}$.
--
--   Under these assumptions the conclusion is as follows. Let $a_1,a_2\in\mathbb{C}$ with $a_1a_2\neq 0$. Let $W_2\colon\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W_2(n(x)g)=\psi_{\mathrm{std},v}(x)W_2(g)$ for the unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the place-$v$ embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of the adelic subgroup `finiteLevelOne` for the ideal $\top$; $W_2(1)=1$; $W_2\bigl(g\cdot\mathtt{scalarPi}(\varpi)\bigr)=\dfrac{a_1a_2}{\mathbf{N}v}\,W_2(g)$ for the scalar matrix $\mathrm{diag}(\varpi,\varpi)$; and $W_2\bigl(\mathrm{diag}(\varpi^{m},1)\bigr)=\mathtt{torusFactor}\bigl(\mathbf{N}v,\,a_1+a_2,\,a_1a_2/\mathbf{N}v\bigr)(m)$ for all $m\in\mathbb{Z}$, where `torusFactor` vanishes for $m<0$ and for $m\ge 0$ is given by the Hecke recursion $c_0=1$, $c_1=\lambda/N$, $c_{m+2}=(\lambda c_{m+1}-\omega c_m)/N$. Let $W_2^{\vee}$ satisfy the same four conditions with $\psi_{\mathrm{std},v}$ replaced by its inverse, $W_2^{\vee}(1)=1$, scalar translation acting by $\mathbf{N}v/(a_1a_2)$, and torus values $\mathtt{torusFactor}\bigl(\mathbf{N}v,\,\mathbf{N}v(a_1+a_2)/(a_1a_2),\,\mathbf{N}v/(a_1a_2)\bigr)(m)$.
--
--   Then, with $\mathrm{GL}_2(\mathbb{Q}_v)$ carrying the Borel $\sigma$-algebra `localGLBorel ℚ v`, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$, every Haar measure $\mu_N$ on the range $N$ of `unipotentGL2Hom` (the subgroup of matrices $n(x)$), and every $W'\in\langle W\rangle$, there exist polynomials `p`, `q`, `pd`, `qd` over $\mathbb{C}$ and reals $\sigma_2,\sigma_3$ with `q` $\neq 0$ and `qd` $\neq 0$ such that all of the following hold, the measure throughout being $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ relative to $\mu_N$:
--
--   1.
--
--   For $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W'(\iota(g))\,W_2(g)\,|\det g|_v^{\,s-1/2}$ is integrable, $\iota$ being the block embedding `iotaGL` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ with last diagonal entry $1$.
--
--   2.
--
--   For $\mathrm{Re}(1-s)>\sigma_3$ the function $g\mapsto \mathtt{dualWhittakerFn3}\,W'\bigl(\iota(g)\cdot\iota(\mathtt{scalarPi}(\varpi)^{-\ell})\bigr)\,W_2^{\vee}(g)\,|\det g|_v^{\,(1-s)-1/2}$ is integrable.
--
--   3.
--
--   For $\mathrm{Re}\,s>\sigma_2$, the Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) taken with $\delta(g)=|\det g|_v$, at $s$, with the pair $\bigl(g\mapsto W'(\iota(g)),\,W_2\bigr)$, satisfies
--   $$\Psi(s)\cdot \mathtt{q}(\mathbf{N}v^{-s})=\mathtt{p}(\mathbf{N}v^{-s}).$$
--
--   4.
--
--   For $\mathrm{Re}(1-s)>\sigma_3$, the same integral at $1-s$ with the pair $\bigl(g\mapsto \mathtt{dualWhittakerFn3}\,W'(\iota(g)\cdot\iota(\mathtt{scalarPi}(\varpi)^{-\ell})),\,W_2^{\vee}\bigr)$ satisfies
--   $$\Psi^{\vee}(1-s)\cdot \mathtt{qd}(\mathbf{N}v^{-(1-s)})=\mathtt{pd}(\mathbf{N}v^{-(1-s)}).$$
--
--   5.
--
--   For every $s\in\mathbb{C}$, with no restriction on $s$,
--   $$\mathtt{pd}(\mathbf{N}v^{-(1-s)})\,\mathtt{q}(\mathbf{N}v^{-s})\,E^{\vee}\bigl(a_1^{-1}\mathbf{N}v^{-(1/2-s)}\bigr)E^{\vee}\bigl(a_2^{-1}\mathbf{N}v^{-(1/2-s)}\bigr)=\mathtt{p}(\mathbf{N}v^{-s})\,\mathtt{qd}(\mathbf{N}v^{-(1-s)})\,E\bigl(a_1\mathbf{N}v^{-(s+1/2)}\bigr)E\bigl(a_2\mathbf{N}v^{-(s+1/2)}\bigr)\varepsilon^{2}.$$
--
--   By comparison with the single-function form `rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge`, no normalisation $W(1)=1$ is imposed here, and the four assertions are made for every member $W'$ of the cyclic space $\langle W\rangle$ simultaneously, with the polynomials and abscissae allowed to depend on $W'$.
--
--   This is the local Rankin–Selberg functional equation for $\mathrm{GL}_3\times\mathrm{GL}_2$ at a finite place, in a rationality-plus-functional-equation shape tied to prescribed Euler data $E$, $E^{\vee}$, $\varepsilon$, $\ell$ on the $\mathrm{GL}_3$ side and to Satake parameters $a_1,a_2$ on the spherical $\mathrm{GL}_2$ side, stated uniformly over the cyclic space generated by the $\mathrm{GL}_3$ Whittaker function. In the cubic-induction part of the Langlands–Tunnell argument it supplies the bad-place input for the analytic properties of the Rankin–Selberg $L$-function of the induced representation, and it is used by the statements producing members of the cyclic space with prescribed congruence-level and torus behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem
LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∀ W' ∈ gl3CyclicSubspace W,
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W' (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 W' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W' (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 W' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
      (∀ s : ℂ,
        pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            Ed.eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) *
            Ed.eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
            E.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            ε ^ 2) := by sorry
