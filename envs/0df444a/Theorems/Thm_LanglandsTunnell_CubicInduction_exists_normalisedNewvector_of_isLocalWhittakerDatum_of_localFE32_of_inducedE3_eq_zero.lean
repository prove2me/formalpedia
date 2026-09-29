-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_inducedE3_eq_zero
-- name    : LanglandsTunnell.CubicInduction.exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_inducedE3_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/37381e8f-1222-5681-83c9-27a0bcd2ef14
-- title:
--   Normalised K₁(v^ℓ)-newvector with prescribed Rankin–Selberg integral
-- statement:
--   Setting. Let $K$ be a number field with $[K:\mathbb{Q}]=3$ (the hypothesis `hdeg`), whose ring of integers is an integral algebra over $\mathcal{O}_{\mathbb{Q}}$, let $\mu\colon(\mathbb{A}_K^\times)\to\mathbb{C}^\times$ be a homomorphism of the idele units which is an admissible twist (`hμ`), i.e. trivial on the image of $K^\times$, continuous, and unitary in the sense that $\lVert\mu(x)\rVert=1$ for every idele unit $x$. Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for its completion, $\mathcal{O}_v$ for the valuation ring, $q_v=$ `Ideal.absNorm v.asIdeal`, and let $\psi_v=$ [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) be the local component at $v$ of the standard additive character of $\mathbb{A}_{\mathbb{Q}}$. Let $\ell\ge 1$ be a natural number (`hℓ`). For a family of complex coefficients $c$ on the primes of $\mathcal{O}_K$, `inducedEulerPoly ℚ c v` is the finite product $\prod_{\mathfrak{P}\mid v}\bigl(1-c(\mathfrak{P})X^{f(\mathfrak{P})}\bigr)$ over the primes $\mathfrak{P}$ of $\mathcal{O}_K$ lying under $v$, $f(\mathfrak{P})$ being the inertia degree, and `inducedCoeff K μ` is the family $\mathfrak{P}\mapsto\mu(\text{uniformizerIdele}\,\mathfrak{P})$ when $\mu$ is unramified at $\mathfrak{P}$ and $0$ otherwise. Write $E=$ `inducedEulerPoly ℚ (inducedCoeff K μ) v` and $E^{\vee}=$ `inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v`. The hypothesis `h3` asserts `inducedE3 ℚ (inducedCoeff K μ) v = 0`, i.e. the coefficient of $X^3$ in $E$ vanishes (`inducedE3` is minus that coefficient).
--
--   The $\mathrm{GL}_3$ datum. Let $W_0\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function which is a local Whittaker datum for $\psi_v^{-1}$ (`h₀`), that is: $W_0(\text{upperUnipotent3}\,x\,y\,z\cdot g)=\psi_v^{-1}(x+y)W_0(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$; $W_0(1)=1$; the multiplicity-one clause `HasWhittakerMultOne`, namely the predicate `GL3WhittakerUniquenessStatement` for the right-translation representation `gl3CyclicRep W₀` and $\psi_v^{-1}$; every nonzero $F$ in the cyclic space `gl3CyclicSubspace W₀` (the $\mathbb{C}$-span of the right translates $h\mapsto W_0(hg)$) has $W_0$ in its own cyclic space; some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ fixes $W_0$ under right translation; and for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $F$ in the cyclic space of $W_0$ which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. The hypothesis `hZ` is a central congruence invariance: for every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ and every unit $d$ of $\mathbb{Q}_v$ with $\lvert d\rvert=1$ and $\lvert d-1\rvert\le$ `WithZero.exp (-(ℓ:ℤ))`, one has $W_0(g\cdot d I_3)=W_0(g)$. Finally $\varepsilon\in\mathbb{C}$ with $\varepsilon\ne 0$ (`hε`).
--
--   The functional-equation hypothesis `hdat`. It is required that for every $\varpi\in\mathcal{O}_v$ whose image $\pi$ in $\mathbb{Q}_v$ is nonzero and satisfies $\lvert\pi\rvert=$ `WithZero.exp (-1 : ℤ)` (a uniformiser), for all $a_1,a_2\in\mathbb{C}$ with $a_1a_2\ne0$, and for every pair of functions $W_2,W_2^{\vee}\colon\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ subject to two groups of five normalisation clauses, the following holds. The clauses on $W_2$: $W_2(u(x)g)=\psi_v(x)W_2(g)$ for the upper unipotent $u(x)$; right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the embedding of $\mathrm{GL}_2(\mathbb{Q}_v)$ into $\mathrm{GL}_2$ of the finite adeles of the level-one subgroup at the unit ideal; $W_2(1)=1$; the central relation $W_2(g\cdot\pi I_2)=\tfrac{a_1a_2}{q_v}W_2(g)$; and the torus values $W_2(\mathrm{diag}(\pi^m,1))=$ `torusFactor` $q_v\,(a_1+a_2)\,(a_1a_2/q_v)\,m$ for all $m\in\mathbb{Z}$, where `torusFactor` is given by the Hecke recursion $c_0=1$, $c_1=\lambda/N$, $Nc_{m+2}=\lambda c_{m+1}-\omega c_m$ for $m\ge 0$ and vanishes for $m<0$. The mirror clauses on $W_2^{\vee}$ are the same with $\psi_v$ replaced by $\psi_v^{-1}$, the central factor $\tfrac{a_1a_2}{q_v}$ replaced by $\tfrac{q_v}{a_1a_2}$, and the torus values given by `torusFactor` $q_v\,\bigl(q_v(a_1+a_2)/(a_1a_2)\bigr)\,\bigl(q_v/(a_1a_2)\bigr)\,m$. Then, with $\mathrm{GL}_2(\mathbb{Q}_v)$ carrying its Borel $\sigma$-algebra, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$, every Haar measure $\mu_N$ on the range $N$ of `unipotentGL2Hom` (the upper unipotent subgroup), and every $W$ in `gl3CyclicSubspace W₀`, there exist polynomials $p,q,p^{\vee},q^{\vee}\in\mathbb{C}[X]$ and reals $\sigma_2,\sigma_3$ with $q\ne0$, $q^{\vee}\ne0$ such that, writing $\nu=\mu_2$ re-weighted by [`HaarQuotient.density N μN`](def/HaarQuotient.html#L25) (the density used to integrate over $N\backslash\mathrm{GL}_2$), $\iota$ for the block embedding `iotaGL` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, $\delta(g)=$ `modulus` $(\det g)$, and $\widetilde{W}=$ `dualWhittakerFn3 W`, $\widetilde{W}(h)=W(w_3\,{}^{t}h^{-1})$ with $w_3$ the antidiagonal permutation matrix `longWeyl3`: (i) for $\operatorname{Re}s>\sigma_2$ the function $g\mapsto W(\iota g)W_2(g)\delta(g)^{s-1/2}$ is $\nu$-integrable; (ii) for $\operatorname{Re}(1-s)>\sigma_3$ the function $g\mapsto \widetilde{W}\bigl(\iota g\cdot\iota((\pi I_2)^{-\ell})\bigr)W_2^{\vee}(g)\delta(g)^{1-s-1/2}$ is $\nu$-integrable; (iii) for $\operatorname{Re}s>\sigma_2$, $\Psi(s,W\circ\iota,W_2)\,q(q_v^{-s})=p(q_v^{-s})$, where $\Psi$ denotes [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) $\mu_2\,N\,\mu_N\,\delta$, i.e. $\int (W_1F)\delta^{s-1/2}\,d\nu$; (iv) for $\operatorname{Re}(1-s)>\sigma_3$, $\Psi\bigl(1-s,\widetilde{W}(\iota(\cdot)\iota((\pi I_2)^{-\ell})),W_2^{\vee}\bigr)\,q^{\vee}(q_v^{-(1-s)})=p^{\vee}(q_v^{-(1-s)})$; and (v) for all $s\in\mathbb{C}$,
--   $$p^{\vee}(q_v^{-(1-s)})\,q(q_v^{-s})\,E^{\vee}\bigl(a_1^{-1}q_v^{-(1/2-s)}\bigr)E^{\vee}\bigl(a_2^{-1}q_v^{-(1/2-s)}\bigr)=p(q_v^{-s})\,q^{\vee}(q_v^{-(1-s)})\,E\bigl(a_1q_v^{-(s+1/2)}\bigr)E\bigl(a_2q_v^{-(s+1/2)}\bigr)\varepsilon^{2}.$$
--
--   Conclusion. Under these hypotheses there exists $W$ in `gl3CyclicSubspace W₀` with the following three properties. First, $W$ is right invariant under the mirabolic congruence set `congruenceK1 (𝓞 ℚ) ℚ v ℓ`: for every $k$ such that $k$ and $k^{-1}$ have all entries of valuation $\le1$ and such that $\lvert k_{2,0}\rvert,\lvert k_{2,1}\rvert,\lvert k_{2,2}-1\rvert\le$ `WithZero.exp (-(ℓ:ℤ))`, and every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$, one has $W(gk)=W(g)$. Secondly, $W(1)=1$. Thirdly, for every uniformiser $\varpi$ as above, all $a_1,a_2\in\mathbb{C}$ with $a_1a_2\ne0$, and every $W_2$ satisfying exactly the five normalisation clauses listed above ($\psi_v$-equivariance, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), $W_2(1)=1$, the central relation with factor $a_1a_2/q_v$, and the `torusFactor` values), and for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ with its Borel $\sigma$-algebra and every Haar measure $\mu_N$ on the unipotent subgroup $N$, there is a real $\sigma_2$ such that: for $\operatorname{Re}s>\sigma_2$ the function $g\mapsto W(\iota g)W_2(g)\delta(g)^{s-1/2}$ is integrable against $\nu=\mu_2$ re-weighted by [`HaarQuotient.density N μN`](def/HaarQuotient.html#L25); and for $\operatorname{Re}s>\sigma_2$,
--   $$\Psi\bigl(s,W\circ\iota,W_2\bigr)\cdot E\bigl(a_1q_v^{-(s+1/2)}\bigr)\cdot E\bigl(a_2q_v^{-(s+1/2)}\bigr)=\nu\bigl(\{g:\exists n\in N,\ \exists k\in \text{localLevelOne}(\top),\ g=nk\}\bigr),$$
--   the right-hand side being the real number `toReal` of that $\nu$-measure, cast into $\mathbb{C}$. Thus the dual-side data ($\sigma_3$, the translated dual integral, and the polynomials $p,q,p^{\vee},q^{\vee}$) occur only in the hypothesis `hdat` and not in the conclusion, where the rational functional equation has been converted into the closed formula above.
--
--   This is the local step, at a finite place $v$ of $\mathbb{Q}$, of the construction of a newvector in the Whittaker model of the local component of the automorphic representation induced from a cubic field: from a rational-form $\mathrm{GL}_3\times\mathrm{GL}_2$ local functional equation for the whole cyclic space of $W_0$, together with the vanishing of the cubic coefficient of the induced Euler polynomial at $v$, it produces a vector fixed by the mirabolic congruence subgroup of level $\ell$, normalised at the identity, whose Rankin–Selberg integrals against normalised spherical $\mathrm{GL}_2$ Whittaker functions are the expected local factor $\bigl(E(a_1q_v^{-(s+1/2)})E(a_2q_v^{-(s+1/2)})\bigr)^{-1}$ up to the volume of $N\cdot K$. It is a level-explicit variant, with the level $\ell$ and the constant $\varepsilon$ as free data, and is used in the construction of a global vector of bounded principal level in the cubic-induction (Langlands–Tunnell) part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_inducedE3_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_inducedE3_eq_zero
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (h3 : LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v = 0)
    (W₀ : LocalGL3 v → ℂ) (h₀ : IsLocalWhittakerDatum v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀)
    (hZ : ∀ (g : LocalGL3 v) (d : (v.adicCompletion ℚ)ˣ), Valued.v (d : v.adicCompletion ℚ) = 1 →
      Valued.v ((d : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(ℓ : ℤ)) →
      W₀ (g * Matrix.GeneralLinearGroup.scalar (Fin 3) d) = W₀ g)
    (ε : ℂ) (hε : ε ≠ 0)
    (hdat :
          ∀ {ϖ : v.adicCompletionIntegers ℚ}
            (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
            Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
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
            ∀ W ∈ gl3CyclicSubspace W₀,
            ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
              (∀ s : ℂ, σ₂ < s.re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (W (iotaGL g) * W₂ g) *
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                          (-(ℓ : ℤ)))) * W₂d g) *
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₂ < s.re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    (1 - s) (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL
                        (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                        (-(ℓ : ℤ))))) W₂d *
                    qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
                  pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
              (∀ s : ℂ,
                pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))
                      *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    ε ^ 2)):
    ∃ W ∈ gl3CyclicSubspace W₀,
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (ℓ), ∀ g, W (g * k) = W g) ∧
      W 1 = 1 ∧
      (∀ {ϖ : v.adicCompletionIntegers ℚ}
        (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
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
          torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
        letI := localGLBorel ℚ v
        haveI := borelSpace_localGLBorel ℚ v
        ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
        ∃ σ₂ : ℝ,
          (∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (W (iotaGL g) * W₂ g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                s (fun g => W (iotaGL g)) W₂ *
                (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                    2))) *
                (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                    2))) =
              (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                  {g : GL (Fin 2) (v.adicCompletion ℚ) |
                    ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ))) := by sorry
