-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittakerFn3_localLevelOne_and_torusValues_const_sq_of_localRankinSelbergFE
-- name    : LanglandsTunnell.CubicInduction.dualWhittakerFn3_localLevelOne_and_torusValues_const_sq_of_localRankinSelbergFE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9ac8d5f3-cbf8-5a3a-a278-cedd6959ccd3
-- title:
--   Level-one invariance and torus table for a dual GL₃ Whittaker function
-- statement:
--   Setting. Let $K$ be a number field, integral over $\mathbb{Z}$ through a fixed algebra structure $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$, with $\dim_{\mathbb{Q}}K=3$ (hypothesis `hdeg`). Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$, let $\mu$ be a homomorphism from the idele group of $K$ to $\mathbb{C}^\times$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$. Write $N=\operatorname{absNorm}(v)$, write $\mathbb{Q}_v$ for the completion at $v$, and write $\psi_v=$ `psiLoc ψ v` for the composite of $\psi$ with the embedding of $\mathbb{Q}_v$ into the adeles supported at $v$. Two conditions on $v$ are imposed: `hv`, that no prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying over $v$ (i.e. with $\mathfrak{P}$ contracting to $v$) has ramification index $\neq 1$; and `hψ`, that $\psi_v$ equals the inverse of the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65).
--
--   The $\mathrm{GL}_3$ vector. Let $W_3:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function subject to three hypotheses. First, `hW₃law`: $W_3$ is a $\psi_v$-Whittaker function, $W_3(u(x,y,z)g)=\psi_v(x+y)\,W_3(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y$ on the superdiagonal and $z$ in position $(1,3)$. Second, `hW₃K`: $W_3(gk)=W_3(g)$ for every $k$ in the set `congruenceK1 (𝓞 ℚ) ℚ v c` with $c=$ `inducedLevelAt K μ v`, that is, every $k$ whose entries and whose inverse's entries all have valuation $\le 1$ and which satisfies $|k_{20}|,|k_{21}|\le \exp(-c)$ and $|k_{22}-1|\le\exp(-c)$; here $c=\sum_{\mathfrak{P}\mid v} f(\mathfrak{P}/v)\,a(\mu_{\mathfrak{P}})$ is the sum over the primes of $K$ above $v$ of the inertia degree times the conductor exponent of the local component of $\mu$. Third, `hDt`, the predicate `HasSphericalTorusValuesAt (inducedCoeff K μ) v W₃`, consisting of two clauses: for every $n\in\mathbb{N}$, $W_3$ at the image under the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ of the scalar $\varpi_v^{\,n}$ equals $N^{-n}h_n$, and for $k_2+1\le k_1$, $W_3$ at the image of $\operatorname{diag}(\varpi_v^{k_1},\varpi_v^{k_2+1})$ equals $N^{-k_1}\bigl(h_{k_1}h_{k_2+1}-h_{k_1+1}h_{k_2}\bigr)$, where $h_n=$ `sphericalTorusValue` of $e_1,e_2,e_3$, the normalised coefficients ($e_1=-[X]$, $e_2=[X^2]$, $e_3=-[X^3]$) of the induced Euler polynomial $\prod_{\mathfrak{P}\mid v}\bigl(1-\mathrm{c}(\mathfrak{P})X^{f(\mathfrak{P}/v)}\bigr)$ formed from $\mathrm{c}=$ `inducedCoeff K μ` (the value of $\mu$ at a uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified there, and $0$ otherwise), and $h$ obeys $h_0=1$, $h_1=e_1$, $h_2=e_1^2-e_2$, $h_{n+3}=e_1h_{n+2}-e_2h_{n+1}+e_3h_n$.
--
--   Let $\varpi$ be an element of the valuation ring of $\mathbb{Q}_v$ whose image $\pi$ in $\mathbb{Q}_v$ is non-zero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), so $\pi$ is a uniformiser, and let $c_0\in\mathbb{C}$ (the constant called `c` in the statement).
--
--   The functional-equation hypothesis `hFE2`. It is assumed that for all $a_1,a_2\in\mathbb{C}$ with $a_1a_2\neq0$ and all pairs of functions $W_2,W_2^{\vee}:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfying five conditions each, the following holds. For $W_2$: the Whittaker law $W_2(u(x)g)=\psi_{v,\mathrm{std}}(x)W_2(g)$ for the standard local character (`hW₂ψ`); right invariance $W_2(gk)=W_2(g)$ for $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the place-$v$ embedding into $\mathrm{GL}_2$ of the finite adeles of the finite level-one subgroup for the unit ideal (`hW₂K`); the normalisation $W_2(1)=1$ (`hW₂1`); the central law $W_2(g\cdot\operatorname{diag}(\pi,\pi))=\frac{a_1a_2}{N}W_2(g)$ (`hW₂Z`); and the torus values $W_2(\operatorname{diag}(\pi^m,1))=$ `torusFactor` $N\,(a_1+a_2)\,\frac{a_1a_2}{N}\,m$ for all $m\in\mathbb{Z}$, this factor being the Hecke recursion sequence $x_0=1$, $x_1=\lambda/N$, $x_{m+2}=(\lambda x_{m+1}-\omega x_m)/N$ evaluated at $m$ for $m\ge0$ and $0$ for $m<0$ (`hW₂T`). For $W_2^{\vee}$: the same five conditions with $\psi_{v,\mathrm{std}}$ replaced by its inverse, with central factor $N/(a_1a_2)$, and with torus values `torusFactor` $N\,\frac{N(a_1+a_2)}{a_1a_2}\,\frac{N}{a_1a_2}$ (`hW₂dψ`, `hW₂dK`, `hW₂d1`, `hW₂dZ`, `hW₂dT`). Then, for the Borel measurable structure on $\mathrm{GL}_2(\mathbb{Q}_v)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ and every Haar measure $\mu_N$ on the range of the unipotent homomorphism $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, there are polynomials $p,q,p^{\vee},q^{\vee}\in\mathbb{C}[X]$ with $q\neq0$, $q^{\vee}\neq0$, and reals $\sigma_2,\sigma_3$, such that: (i) for $\operatorname{Re}s>\sigma_2$ the function $g\mapsto W_3(\iota g)W_2(g)\,\lVert\det g\rVert^{s-1/2}$ is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$, where $\iota$ is the block embedding and $\lVert\cdot\rVert$ is the module `modulus`; (ii) for $\operatorname{Re}(1-s)>\sigma_3$ the function $g\mapsto (\mathrm{d}W_3)\bigl(\iota g\cdot\iota(\operatorname{diag}(\pi,\pi)^{-c})\bigr)W_2^{\vee}(g)\,\lVert\det g\rVert^{1-s-1/2}$ is integrable against the same measure, where $\mathrm{d}W_3=$ `dualWhittakerFn3 W₃` is $g\mapsto W_3\bigl(w_3\cdot{}^{t}g^{-1}\bigr)$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$; (iii) for $\operatorname{Re}s>\sigma_2$ the Rankin–Selberg local integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) at $s$ of $W_3\circ\iota$ against $W_2$, with $\delta=\lVert\det\cdot\rVert$, times $q(N^{-s})$ equals $p(N^{-s})$; (iv) for $\operatorname{Re}(1-s)>\sigma_3$ the same local integral at $1-s$ of the shifted dual $g\mapsto(\mathrm{d}W_3)(\iota g\cdot\iota(\operatorname{diag}(\pi,\pi)^{-c}))$ against $W_2^{\vee}$, times $q^{\vee}(N^{-(1-s)})$, equals $p^{\vee}(N^{-(1-s)})$; and (v) for every $s\in\mathbb{C}$,
--   $$p^{\vee}(N^{-(1-s)})\,q(N^{-s})\,E_{\mu^{-1}}\!\bigl(a_1^{-1}N^{-(1/2-s)}\bigr)E_{\mu^{-1}}\!\bigl(a_2^{-1}N^{-(1/2-s)}\bigr)=p(N^{-s})\,q^{\vee}(N^{-(1-s)})\,E_{\mu}\!\bigl(a_1N^{-(s+1/2)}\bigr)E_{\mu}\!\bigl(a_2N^{-(s+1/2)}\bigr)\cdot\Bigl(c_0\bigl(\textstyle\prod_{w\mid v}\mu_w(-1)\bigr)\bigl(\prod_{w\mid v}\varepsilon_w\bigr)\Bigr)^{2},$$
--   where $E_{\mu}$ and $E_{\mu^{-1}}$ are the induced Euler polynomials at $v$ formed from `inducedCoeff K μ` and `inducedCoeff K μ⁻¹`, the products are the finite products over the primes $w$ of $K$ above $v$, $\mu_w$ is the local component `localChar μ w`, and $\varepsilon_w=$ `stdRootNumberAt K w (localChar μ w)` is the standard local root number, the value at $s=1/2$ of the standard local epsilon factor of $\mu_w$.
--
--   Conclusion. Under these hypotheses there exist functions $u:\mathbb{N}\times\mathbb{N}\to\mathbb{C}$ and $u^{\mathbb{Z}}:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$ with the following seven properties, where now $h^{\vee}_n$ denotes `sphericalTorusValue` of the induced coefficients $e_1,e_2,e_3$ at $v$ formed from `inducedCoeff K μ⁻¹`.
--
--   1. $u(k,0)=h^{\vee}_k$ for every $k\in\mathbb{N}$.
--
--   2. $u(k_1,k_2+1)=h^{\vee}_{k_1}h^{\vee}_{k_2+1}-h^{\vee}_{k_1+1}h^{\vee}_{k_2}$ for all $k_1,k_2\in\mathbb{N}$.
--
--   3. $u^{\mathbb{Z}}(m_1,m_2)=0$ whenever $m_2<0$ or $m_1<m_2$.
--
--   4. $u^{\mathbb{Z}}(k_1,k_2)=u(k_1,k_2)$ for natural numbers $k_2\le k_1$.
--
--   5. Level-one invariance of the shifted dual: for every $x\in\mathrm{GL}_2(\mathbb{Q}_v)$ lying in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) and every $h\in\mathrm{GL}_3(\mathbb{Q}_v)$,
--   $(\mathrm{d}W_3)\bigl(h\,\iota(x)\,\iota(\operatorname{diag}(\pi,\pi)^{-c})\bigr)=(\mathrm{d}W_3)\bigl(h\,\iota(\operatorname{diag}(\pi,\pi)^{-c})\bigr)$.
--
--   6. Torus table: for all $m_1,m_2\in\mathbb{Z}$,
--   $$(\mathrm{d}W_3)\Bigl(\iota\bigl(\operatorname{diag}(\pi^{m_1-m_2},1)\cdot\operatorname{diag}(\pi,\pi)^{m_2}\bigr)\cdot\iota\bigl(\operatorname{diag}(\pi,\pi)^{-c}\bigr)\Bigr)=\Bigl(c_0\prod_{w\mid v}\varepsilon_w\Bigr)^{2}N^{-m_1}\,u^{\mathbb{Z}}(m_1,m_2),$$
--   the constant here involving the root numbers only, without the factors $\mu_w(-1)$ that occur in `hFE2`.
--
--   7. Whittaker law of the shifted dual along the $\mathrm{GL}_2$ unipotent: for all $x\in\mathbb{Q}_v$ and $g\in\mathrm{GL}_2(\mathbb{Q}_v)$,
--   $(\mathrm{d}W_3)\bigl(\iota(u(x)g)\,\iota(\operatorname{diag}(\pi,\pi)^{-c})\bigr)=\psi_v^{-1}(x)\,(\mathrm{d}W_3)\bigl(\iota(g)\,\iota(\operatorname{diag}(\pi,\pi)^{-c})\bigr)$.
--
--   This is the local step at a finite place $v$ of $\mathbb{Q}$ unramified in the cubic field $K$ in the converse-theorem analysis of the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg integrals: from the assumed local functional equations against all spherical $\mathrm{GL}_2$ Whittaker pairs with Hecke parameters $(a_1,a_2)$, it extracts the behaviour of the dual Whittaker function translated by the scalar $\varpi^{-c}$, namely its invariance under the local level-one subgroup, its $\psi_v^{-1}$-equivariance along the $\mathrm{GL}_2$ unipotent, and a complete table of its values on the diagonal torus in terms of the spherical torus values attached to $\mu^{-1}$. It feeds the construction of the Rankin–Selberg $L$-function with its archimedean factor and the global identity expressing sums over cells in terms of root-number monomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualWhittakerFn3_localLevelOne_and_torusValues_const_sq_of_localRankinSelbergFE.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.dualWhittakerFn3_localLevelOne_and_torusValues_const_sq_of_localRankinSelbergFE
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ IsRamifiedIn K v) (hψ : psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)

    (W₃ : LocalGL3 v → ℂ) (hW₃law : IsGL3PsiWhittakerFn (psiLoc ψ v) W₃)
    (hW₃K : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g : LocalGL3 v, W₃ (g * k) = W₃ g)
    (hDt : HasSphericalTorusValuesAt (inducedCoeff K μ) v W₃)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (c : ℂ)
    (hFE2 :
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
      ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
        (∀ s : ℂ, σ₂ < s.re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
        (∀ s : ℂ, σ₃ < (1 - s).re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    (-(inducedLevelAt K μ v : ℤ)))) * W₂d g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W₃ (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < (1 - s).re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              (1 - s) (fun g => dualWhittakerFn3 W₃ (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(inducedLevelAt K μ v : ℤ))))) W₂d *
              qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
            pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
        (∀ s : ℂ,
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
              (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                  s))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                  s))) =
            p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
              (c * ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
                ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w))) ^ 2)) :
    ∃ (u : ℕ → ℕ → ℂ) (uZ : ℤ → ℤ → ℂ),
      (∀ k : ℕ, u k 0 = sphericalTorusValue (inducedE1 ℚ (inducedCoeff K μ⁻¹) v)
          (inducedE2 ℚ (inducedCoeff K μ⁻¹) v) (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) k) ∧
      (∀ k₁ k₂ : ℕ, u k₁ (k₂ + 1) =
        sphericalTorusValue (inducedE1 ℚ (inducedCoeff K μ⁻¹) v) (inducedE2 ℚ (inducedCoeff K μ⁻¹) v)
          (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) k₁ *
            sphericalTorusValue (inducedE1 ℚ (inducedCoeff K μ⁻¹) v) (inducedE2 ℚ (inducedCoeff K μ⁻¹) v)
              (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) (k₂ + 1) -
          sphericalTorusValue (inducedE1 ℚ (inducedCoeff K μ⁻¹) v) (inducedE2 ℚ (inducedCoeff K μ⁻¹) v)
            (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) (k₁ + 1) *
            sphericalTorusValue (inducedE1 ℚ (inducedCoeff K μ⁻¹) v) (inducedE2 ℚ (inducedCoeff K μ⁻¹) v)
              (inducedE3 ℚ (inducedCoeff K μ⁻¹) v) k₂) ∧
      (∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0) ∧
      (∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = u k₁ k₂) ∧
      (∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (h : LocalGL3 v),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          dualWhittakerFn3 W₃ (h * iotaGL x *
            iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(inducedLevelAt K μ v : ℤ)))) =
            dualWhittakerFn3 W₃ (h *
              iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(inducedLevelAt K μ v : ℤ))))) ∧
      (∀ m₁ m₂ : ℤ,
        dualWhittakerFn3 W₃
            (iotaGL
                (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                    (m₁ - m₂) *
                  UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    m₂) *
              iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(inducedLevelAt K μ v : ℤ)))) =
          (c * ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w)) ^ 2 *
            ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ m₁ * uZ m₁ m₂)) ∧
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        dualWhittakerFn3 W₃ (iotaGL (unipotent x * g) *
            iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(inducedLevelAt K μ v : ℤ)))) =
          (psiLoc ψ v)⁻¹ x * dualWhittakerFn3 W₃ (iotaGL g *
            iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(inducedLevelAt K μ v : ℤ))))) := by sorry
