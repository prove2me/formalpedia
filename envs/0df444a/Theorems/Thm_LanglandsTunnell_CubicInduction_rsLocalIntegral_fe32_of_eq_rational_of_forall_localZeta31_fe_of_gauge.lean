-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d1701fb1-1ddc-5e46-8042-d5e093469240
-- title:
--   Local γ-factor identity for GL₃× GL₂ with gauge majorant
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $\mathbb{Q}_v$ for the completion, $N=\mathrm{absNorm}(v)$ for the residue norm, and let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$ assumed (hypothesis `hψinv`) to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). Let $W\colon GL_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function subject to the following groups of hypotheses.
--
--   Whittaker and representation-theoretic hypotheses: `hW` states that $W$ is a $\psi_v$-Whittaker function in the sense of `IsGL3PsiWhittakerFn`, i.e. $W(u(x,y,z)g)=\psi_v(x+y)\,W(g)$ for the upper unipotent matrix $u(x,y,z)=\begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$ and all $g$; `hW1` normalises $W(1)=1$; `hmult` is `HasWhittakerMultOne`, namely that the space of $\psi_v$-Whittaker functionals of the representation of $GL_3(\mathbb{Q}_v)$ by right translation on the span `gl3CyclicSubspace W` of the right translates of $W$ has rank at most $1$ over $\mathbb{C}$; `hirr` is the irreducibility-type condition that every $F\neq 0$ in `gl3CyclicSubspace W` has $W$ in its own cyclic span `gl3CyclicSubspace F`; `hsm` (smoothness) asserts the existence of an open subgroup $U_v\le GL_3(\mathbb{Q}_v)$ with $W(gk)=W(g)$ for all $k\in U_v$ and all $g$; `hadm` (admissibility) asserts that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $F\in$ `gl3CyclicSubspace W` which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$.
--
--   Gauge hypothesis `hWgauge`: there are $B\in\mathbb{R}$, $t\in\mathbb{N}$ and $C\in\mathbb{R}$ such that, writing for $h\in GL_3(\mathbb{Q}_v)$
--   $$X(h)=\frac{\mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)}{\mathrm{minorSup}(h)^2},\qquad Y(h)=\frac{\mathrm{minorSup}(h)}{\mathrm{lastRowSup}(h)^2},$$ where $\mathrm{detSize}(h)=\|\det h\|$, $\mathrm{lastRowSup}(h)$ is the maximum of the norms of the three entries of the bottom row of $h$ and $\mathrm{minorSup}(h)$ the maximum of the norms of the three $2\times 2$ minors formed from the last two rows, one has: $W(h)=0$ whenever it is not the case that both $X(h)\le B$ and $Y(h)\le B$, and $\|W(h)\|\le C/(X(h)\,Y(h))^{t}$ whenever $X(h)\le B$ and $Y(h)\le B$.
--
--   Central character hypotheses: $\omega_v\colon \mathbb{Q}_v^\times\to\mathbb{C}^\times$ is a group homomorphism with $\|\omega_v(z)\|=1$ for all $z$ (`hωu`), and $W(\mathrm{scalar}(t)\,h)=\omega_v(t)\,W(h)$ for all $t\in\mathbb{Q}_v^\times$ and all $h$ (`hω`).
--
--   Uniformiser: $\varpi$ is an element of the valuation ring of $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`).
--
--   Local $GL_3\times GL_1$ data: $E,E^\vee\in\mathbb{C}[T]$ (the Lean names are `E` and `Ed`), $\varepsilon\in\mathbb{C}$ and $\ell\in\mathbb{N}$, subject to `h31`: for every $g\in GL_3(\mathbb{Q}_v)$ there exist a function $P\colon\mathbb{C}\to\mathbb{C}$ and reals $\sigma_0,\sigma_1$ such that (i) $P$ is rational in $N^{-s}$ up to a monomial shift: there are polynomials $Q,R$ with $R\neq0$ and an $m\in\mathbb{N}$ with $P(s)\,R(N^{-s})=Q(N^{-s})\,N^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` holds above $\sigma_0$, i.e. for $\operatorname{Re}s>\sigma_0$ the function $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\,\mathrm{modulus}(a)^{s-1}$ is integrable against the multiplicative measure obtained by pulling back `mulMeasure (selfDualHaarAt ℚ v)` along $\mathbb{Q}_v^\times\to\mathbb{Q}_v$; (iii) for $\operatorname{Re}s>\sigma_0$, $\mathrm{localZeta30}$ at $(W,\mathbf 1,s,g)$, namely $\int_{\mathbb{Q}_v^\times}W(\iota(\mathrm{diag}(a,1))g)\,\mathrm{modulus}(a)^{s-1}$, equals $E(N^{-s})^{-1}P(s)$; (iv) `IsLocalZeta31ConvergentAbove` holds above $\sigma_1$ for the dual Whittaker function $\widetilde W(h)=W(w_3\,{}^t h^{-1})$ ($w_3$ the long Weyl element of $GL_3$) with trivial character at the point $w'\,{}^t g^{-1}$ ($w'$ the transposition of the last two coordinates), i.e. integrability on $\mathbb{Q}_v^\times\times\mathbb{Q}_v$ of $(a,x)\mapsto\widetilde W(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,w'\,{}^tg^{-1})\,\mathrm{modulus}(a)^{s-1}$ against the product of that multiplicative measure with `selfDualHaarAt ℚ v`; and (v) for all $s$ with $\operatorname{Re}(1-s)>\sigma_1$,
--   $$\mathrm{localZetaDual31}(W,\mathbf 1,1-s,g)=E^\vee\!\left(N^{-(1-s)}\right)^{-1}\left(\varepsilon\, N^{\ell(1/2-s)}\right)P(s),$$ the left-hand side being $\mathrm{localZeta31}$ of $\widetilde W$ with trivial character at $w'\,{}^tg^{-1}$ and argument $1-s$.
--
--   Under these hypotheses the assertion is the following universally quantified statement. Let $a_1,a_2\in\mathbb{C}$ with $a_1a_2\neq0$ (`ha`). Let $W_2\colon GL_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W_2\!\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right)=\mathrm{psiLocal}(x)W_2(g)$ (`hW₂ψ`); right invariance $W_2(gk)=W_2(g)$ for $k$ in the local level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (`hW₂K`); $W_2(1)=1$ (`hW₂1`); $W_2(g\cdot\varpi I_2)=\frac{a_1a_2}{N}W_2(g)$ (`hW₂Z`); and $W_2(\mathrm{diag}(\varpi^m,1))=\mathrm{torusFactor}\,N\,(a_1+a_2)\,\frac{a_1a_2}{N}\,m$ for all $m\in\mathbb{Z}$ (`hW₂T`), where `torusFactor` vanishes for $m<0$ and is given for $m\ge0$ by the Hecke recursion $c_0=1$, $c_1=\lambda/N$, $c_{m+2}=(\lambda c_{m+1}-\omega c_m)/N$. Let $W_2^{d}$ satisfy the corresponding conditions with $\mathrm{psiLocal}^{-1}$ in place of $\mathrm{psiLocal}$ (`hW₂dψ`), the same level-one invariance (`hW₂dK`), $W_2^d(1)=1$ (`hW₂d1`), $W_2^d(g\cdot\varpi I_2)=\frac{N}{a_1a_2}W_2^d(g)$ (`hW₂dZ`), and $W_2^d(\mathrm{diag}(\varpi^m,1))=\mathrm{torusFactor}\,N\,\frac{N(a_1+a_2)}{a_1a_2}\,\frac{N}{a_1a_2}\,m$ (`hW₂dT`).
--
--   Let $\mu_2$ be a Haar measure on $GL_2(\mathbb{Q}_v)$ (for its Borel $\sigma$-algebra) and $\mu_N$ a Haar measure on the range of `unipotentGL2Hom`, the subgroup of upper unipotent matrices; all integrals below are taken against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to that subgroup and $\mu_N$. Let $p,q,p^{d},q^{d}\in\mathbb{C}[T]$ and $\sigma_2,\sigma_3\in\mathbb{R}$ with $q\neq0$ and $q^{d}\neq0$, and assume four hypotheses: for $\operatorname{Re}s>\sigma_2$ the function $g\mapsto W(\iota(g))W_2(g)\,\mathrm{modulus}(\det g)^{s-1/2}$ is integrable against that weighted measure, where $\iota$ is the embedding $g\mapsto\mathrm{diag}(g,1)$ of $GL_2$ into $GL_3$; for $\operatorname{Re}(1-s)>\sigma_3$ the function $g\mapsto\widetilde W\!\left(\iota(g)\,\iota((\varpi I_2)^{-\ell})\right)W_2^{d}(g)\,\mathrm{modulus}(\det g)^{1-s-1/2}$ is integrable against it; for $\operatorname{Re}s>\sigma_2$ the Rankin–Selberg local integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with $\delta(g)=\mathrm{modulus}(\det g)$, argument $s$, and the pair $\bigl(g\mapsto W(\iota g),\,W_2\bigr)$ satisfies $\;\mathrm{rsLocalIntegral}\cdot q(N^{-s})=p(N^{-s})$; and for $\operatorname{Re}(1-s)>\sigma_3$ the same local integral at argument $1-s$ for the pair $\bigl(g\mapsto\widetilde W(\iota(g)\,\iota((\varpi I_2)^{-\ell})),\,W_2^{d}\bigr)$ satisfies $\;\mathrm{rsLocalIntegral}\cdot q^{d}(N^{-(1-s)})=p^{d}(N^{-(1-s)})$.
--
--   The conclusion is the single identity, valid for every $s\in\mathbb{C}$ (with no restriction on $\operatorname{Re}s$):
--   $$p^{d}\!\left(N^{-(1-s)}\right)q\!\left(N^{-s}\right)E^\vee\!\left(a_1^{-1}N^{-(1/2-s)}\right)E^\vee\!\left(a_2^{-1}N^{-(1/2-s)}\right)=p\!\left(N^{-s}\right)q^{d}\!\left(N^{-(1-s)}\right)E\!\left(a_1N^{-(s+1/2)}\right)E\!\left(a_2N^{-(s+1/2)}\right)\varepsilon^{2}.$$
--
--   This is the multiplicativity of the local $\gamma$-factor of $GL_3\times GL_2$ in the $GL_2$ variable, for an unramified partner with Satake parameters $a_1,a_2$, in the shape of Jacquet–Piatetski-Shapiro–Shalika: given that the two Rankin–Selberg local integrals are already known to be rational in $N^{-s}$ with prescribed numerators and denominators, the functional equation of the $GL_3\times GL_1$ integrals with data $(E,E^\vee,\varepsilon,\ell)$ forces the displayed identity of polynomial expressions, which is the local functional equation for $GL_3\times GL_2$. It is the functional-equation half of the local input used by [`LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge), the gauge version in which $W$ is assumed majorised by an explicit two-parameter gauge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge.lean

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
LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
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
    ∀ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 → qd ≠ 0 →
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) →
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) →
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) →
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) →
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
