-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
-- name    : LanglandsTunnell.CubicInduction.exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/e608ef65-cf43-57ab-b5ad-bc0a4734a9ca
-- title:
--   Existence of a dual middle datum at a finite place
-- statement:
--   Throughout, $v$ is a point of the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$, $\mathbb{Q}_v$ denotes `v.adicCompletion ℚ`, $q$ denotes the absolute norm of `v.asIdeal`, and `LocalGL3 v` is $\mathrm{GL}_3(\mathbb{Q}_v)$. The map $\iota =$ `iotaGL` embeds $\mathrm{GL}_2$ into $\mathrm{GL}_3$ as $h \mapsto \mathrm{diag}(h,1)$; `weylPrime3` is the permutation matrix interchanging the second and third coordinates, `longWeyl3` the antidiagonal permutation matrix; `transposeInv3` $g = (g^{-1})^{\mathsf T}$ and `dualWhittakerFn3` $F(g) = F(\mathrm{longWeyl3}\cdot (g^{-1})^{\mathsf T})$; `scalarPi` $\varpi$ is the scalar matrix $\mathrm{diag}(\varpi,\varpi)$ in $\mathrm{GL}_2$, `diagUnitGL2` $x = \mathrm{diag}(x,1)$, `diagUnits2` $x\,y = \mathrm{diag}(x,y)$, `unipotent` $x$ = `unipotentGL2` $x = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and `diagZ` $\varpi\,m = \mathrm{diag}(\varpi^m,1)$. Measures on $\mathbb{Q}_v$, on $\mathbb{Q}_v^{\times}$ and on $\mathrm{GL}_2(\mathbb{Q}_v)$ are taken for the Borel structures `localBorel`, `localGLBorel`; $\tau :=$ `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))` and $\nu :=$ `selfDualHaarAt ℚ v`.
--
--   The data on the $\mathrm{GL}_3$ side are: an additive character $\psi_v$ of $\mathbb{Q}_v$ with `hψinv` asserting $\psi_v = ($[`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65)$)^{-1}$, and a function $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ subject to the following named hypotheses. `hW`: $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for the upper unipotent matrix $u(x,y,z)$ with entries $x,y,z$ and all $g$. `hW1`: $W(1)=1$. `hmult`: the Whittaker functional space of the representation of $\mathrm{GL}_3(\mathbb{Q}_v)$ by right translation on `gl3CyclicSubspace W` (the $\mathbb{C}$-span of the right translates of $W$) relative to $\psi_v$ has rank at most $1$. `hirr`: every nonzero $F$ in `gl3CyclicSubspace W` has $W \in$ `gl3CyclicSubspace F`. `hsm`: there is an open subgroup $U_v \le \mathrm{GL}_3(\mathbb{Q}_v)$ with $W(gk)=W(g)$ for all $k \in U_v$ and all $g$. `hadm`: for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $F \in$ `gl3CyclicSubspace W` that is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. `hWgauge` (gauge majorisation): with $\gamma_1(h) = \|\det h\| \cdot \mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $\gamma_2(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$, where $\mathrm{lastRowSup}$ is the maximum of the norms of the three entries of the bottom row and $\mathrm{minorSup}$ the maximum of the norms of the three $2\times 2$ minors formed from the last two rows, there exist $B \in \mathbb{R}$, $t \in \mathbb{N}$, $C \in \mathbb{R}$ such that for every $h$: $W(h)=0$ unless $\gamma_1(h)\le B$ and $\gamma_2(h)\le B$, and $\|W(h)\| \le C/(\gamma_1(h)\gamma_2(h))^t$ whenever $\gamma_1(h)\le B$ and $\gamma_2(h)\le B$. A homomorphism $\omega_v : \mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$ is given with `hωu`: $\|\omega_v(z)\|=1$ for all $z$, and `hω`: $W(\mathrm{scalar}(t)h) = \omega_v(t)W(h)$. An element $\varpi$ of the valuation ring is given with `hπ`: its image in $\mathbb{Q}_v$ is nonzero, and `hϖ`: that image has valuation $\exp(-1)$, i.e. $\varpi$ is a uniformiser.
--
--   Further, polynomials $E, E^{\vee} \in \mathbb{C}[T]$, a constant $\varepsilon \in \mathbb{C}$ and $\ell \in \mathbb{N}$ are given, together with the hypothesis `h31`: for every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ there are a function $P:\mathbb{C}\to\mathbb{C}$ and reals $\sigma_0,\sigma_1$ such that (i) $P$ is rational in $q^{-s}$ up to a monomial, in the sense that there are polynomials $Q,R$ with $R \neq 0$ and an $m \in \mathbb{N}$ with $P(s)R(q^{-s}) = Q(q^{-s})q^{ms}$ for all $s$; (ii) the $(3,0)$ integrand for $W$, the trivial character and $g$ is $\tau$-integrable for $\mathrm{Re}\,s > \sigma_0$, and there `localZeta30` $v\,\tau\,W\,1\,s\,g = E(q^{-s})^{-1}P(s)$; (iii) the $(3,1)$ integrand for `dualWhittakerFn3` $W$, the trivial character and $\mathrm{weylPrime3}\cdot (g^{-1})^{\mathsf T}$ is $(\tau\otimes\nu)$-integrable for $\mathrm{Re}\,s>\sigma_1$, and for all $s$ with $\sigma_1 < \mathrm{Re}(1-s)$ one has `localZetaDual31` $v\,\tau\,\nu\,W\,1\,(1-s)\,g = E^{\vee}(q^{-(1-s)})^{-1}\bigl(\varepsilon\, q^{\ell(1/2-s)}P(s)\bigr)$.
--
--   Finally, a function $V : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ is given with `hVmem`: $V \in$ `gl3CyclicSubspace W`; `hVK`: $V(g\,\iota(k)) = V(g)$ for all $g$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage under the local embedding of the finite-adelic level-one subgroup at the unit ideal); and `hVdK`: the same right invariance for `dualWhittakerFn3` $V$. Complex numbers $a_1,a_2$ are given with `ha`: $a_1a_2 \neq 0$.
--
--   Under these hypotheses the following holds. Let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(\mathbb{Q}_v)$ and $\mu_N$ a Haar measure on the range of `unipotentGL2Hom`, the upper unipotent subgroup of $\mathrm{GL}_2(\mathbb{Q}_v)$; write $\delta(g) = \mathrm{modulus}(\det g)$ and recall that [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) $\mu_2\,H\,\mu_N\,\delta\,s\,F_1\,F_2 = \int F_1(g)F_2(g)\delta(g)^{s-1/2}$ against $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) $H\,\mu_N$. Let $c_K$ be a real number with $0 < c_K$ (hypothesis `_hcK`) satisfying the unfolding hypothesis `_hK1`: for every additive character $\theta$ of $\mathbb{Q}_v$, every $\theta$-Whittaker function $W$ on $\mathrm{GL}_3(\mathbb{Q}_v)$ in the sense of `IsGL3PsiWhittakerFn` that is right invariant under some open subgroup, every pair of characters $\chi = (\chi_0,\chi_1)$ of $\mathbb{Q}_v^{\times}$, every section $f \in$ `principalSeries2` $v\,\chi$, every $w_0$ whose matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and every $s$: if $g \mapsto W(\iota(g))f(w_0g)\delta(g)^{s-1/2}$ is $\mu_2$-integrable, then $g \mapsto W(\iota(g))\bigl(\int f(w_0\,u(y)\,g)\theta(y)\,d\nu(y)\bigr)\delta(g)^{s-1/2}$ is integrable for the density-weighted measure, and the corresponding `rsLocalIntegral` equals $c_K \int f(w_0 u(y)) \bigl(\int \chi_0(a)\,\mathrm{modulus}(a)^{s-1}\,\mathrm{localZeta31}\,v\,\tau\,\nu\,W\,\chi_1\,s\,(\iota(\mathrm{diag}(1,a)u(y)))\,d\tau(a)\bigr)d\nu(y)$. Let $u \in \mathbb{C}$ satisfy the dominance condition $\|a_1\|q^{-\mathrm{Re}\,u} < \|a_2\|q^{\mathrm{Re}\,u}$, and write $a_1' = a_1q^{-u}$, $a_2' = a_2q^{u}$. Let $W_2^{\vee} : \mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: `hW₂dψ`: $W_2^{\vee}(u(x)g) = \psi_{\mathrm{loc}}^{-1}(x)W_2^{\vee}(g)$ for the inverse of the standard local character; `hW₂dK`: right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); `hW₂d1`: $W_2^{\vee}(1)=1$; `hW₂dZ`: $W_2^{\vee}(g\cdot\mathrm{scalarPi}\,\varpi) = \frac{q}{a_1'a_2'}W_2^{\vee}(g)$; and `hW₂dT`: for every $m \in \mathbb{Z}$, $W_2^{\vee}(\mathrm{diagZ}\,\varpi\,m) = \mathrm{torusFactor}\,q\,\bigl(q(a_1'+a_2')/(a_1'a_2')\bigr)\bigl(q/(a_1'a_2')\bigr)\,m$, that is, the value given by the Hecke recursion `heckeRecursionSeq` with these parameters for $m \ge 0$ and $0$ for $m<0$.
--
--   Then there exist polynomials $m_1^{\vee}, m_2^{\vee} \in \mathbb{C}[T]$, an integer $k^{\vee}$ and a real $\sigma_D$ with $m_2^{\vee}\neq 0$ such that the following two assertions hold.
--
--   First conjunct. Put $\alpha_1 = q^{1/2}(a_1')^{-1}$, $\alpha_2 = q^{1/2}(a_2')^{-1}$, and, for each $s$, $X = \alpha_1^{-1}q^{1-s}$ and $Y = \alpha_2\,\omega_v(\varpi)^{-1}q^{s}$, where $\varpi$ is regarded as a unit of $\mathbb{Q}_v$. Put $\mu_0 = \nu\{x : \mathrm{val}(x)\le 1\}$ (as a real number) and $\mu_1 = \tau\{e : \mathrm{val}(e)=1\}$ (as a real number), and
--   $$C_0(s) = \Bigl(c_K\,\mu_0\,\mu_1^{2}\,\bigl(\mu_0(1-q^{-1}a_1'(a_2')^{-1})\bigr)^{-1}\alpha_1^{-\ell}\Bigr)\,\varepsilon\,q^{\ell(1/2-s)}\,E\bigl(a_1'q^{-(s+1/2)}\bigr)\,E^{\vee}\bigl((a_2')^{-1}q^{-(1/2-s)}\bigr).$$
--   Let $N_b \in \mathbb{Z}$, $D_{b,1},D_{b,2} \in \mathbb{C}[T]$, $P_b \in \mathbb{C}[T_0,T_1]$ and $r_b \in \mathbb{R}$ be such that the two-variable coefficient family
--   $$A_b(n_1,n_2) = V\Bigl(\iota\bigl(\mathrm{scalarPi}\,\varpi^{\,n_2}\cdot\mathrm{diagUnitGL2}(\varpi^{\,n_1})\bigr)\cdot \mathrm{weylPrime3}\cdot\iota\bigl(\mathrm{scalarPi}\,\varpi^{\,\ell}\bigr)\Bigr)$$
--   satisfies: $D_{b,1}(0)\neq 0$, $D_{b,2}(0)\neq 0$, $0<r_b$, $A_b(n)=0$ whenever $n_1<N_b$ or $n_2<N_b$, and for all $X',Y'$ with $\|X'\|<r_b$, $\|Y'\|<r_b$ the double series $\sum_{m}\|A_b(N_b+m_1,N_b+m_2)X'^{m_1}Y'^{m_2}\|$ converges and $\bigl(\sum_m A_b(N_b+m_1,N_b+m_2)X'^{m_1}Y'^{m_2}\bigr)D_{b,1}(X')D_{b,2}(Y') = P_b(X',Y')$. Let $N_t, D_{t,1},D_{t,2},P_t,r_t$ satisfy the same list of conditions for the family $A_t$ obtained by replacing `weylPrime3` by $\mathrm{longWeyl3}\cdot\mathrm{weylPrime3}$ in the displayed formula. Then for every $s \in \mathbb{C}$:
--   $$m_1^{\vee}(q^{-s})\,q^{k^{\vee}s}\,D_{b,1}(X)D_{b,2}(Y)\,D_{t,1}(X)D_{t,2}(Y)\,(1-q^{-1})$$
--   $$= m_2^{\vee}(q^{-s})\,C_0(s)\Bigl(X^{N_b}Y^{N_b}P_b(X,Y)\,D_{t,1}(X)D_{t,2}(Y)(1-q^{-1}) + (1-q^{-1})q^{-1}\,X^{N_t}Y^{N_t}P_t(X,Y)\,D_{b,1}(X)D_{b,2}(Y)\Bigr).$$
--
--   Second conjunct. For every $s$ with $\sigma_D < \mathrm{Re}(1-s)$,
--   $$\mathrm{rsLocalIntegral}\,\mu_2\,N\,\mu_N\,\delta\,(1-s)\ \bigl(g \mapsto \mathrm{dualWhittakerFn3}\,V\bigl(\iota(g)\,\iota(\mathrm{scalarPi}\,\varpi^{-\ell})\bigr)\bigr)\ W_2^{\vee}\cdot E^{\vee}\bigl((a_1')^{-1}q^{-(1/2-s)}\bigr)E^{\vee}\bigl((a_2')^{-1}q^{-(1/2-s)}\bigr)m_2^{\vee}(q^{-s}) = m_1^{\vee}(q^{-s})\,q^{k^{\vee}s},$$
--   where $N$ is the range of `unipotentGL2Hom`. Thus the same pair $(m_1^{\vee},m_2^{\vee},k^{\vee})$ both solves the rational identity of the first conjunct for all presentations of the two torus series and computes the dual local Rankin–Selberg integral of $V$ against $W_2^{\vee}$ in the right half plane $\sigma_D < \mathrm{Re}(1-s)$.
--
--   This is the dual half of the 'common middle' of the local $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg functional equation at a finite place, in the form used on the rational-torus route: a single datum $(m_1^{\vee},m_2^{\vee},k^{\vee})$ which is simultaneously determined by the rational presentations of the two torus series attached to $V$ and evaluates the dual local integral. It is used by [`LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge), where it is matched against the corresponding identity for the unconjugated integral to produce the local functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
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
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ (cK : ℝ) (_hcK : 0 < cK)
      (_hK1 : ∀ (θ : AddChar (v.adicCompletion ℚ) ℂ)
          (W : LocalGL3 v → ℂ) (_hW : IsGL3PsiWhittakerFn θ W)
          (_hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
          (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
          (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 v χ)
          (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
          (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
          (s : ℂ),
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * f (w₀ * g)) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2)) μ₂ →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * (∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v))) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) (fun g => ∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v)) =
            (cK : ℂ) * ∫ y, f (w₀ * unipotentGL2 y) *
              (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
                localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)),
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m),
      ∃ (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σD : ℝ), m₂d ≠ 0 ∧
      (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Db₁.eval 0 ≠ 0 ∧ Db₂.eval 0 ≠ 0 ∧ 0 < rb ∧
          (∀ n : ℤ × ℤ, (n.1 < Nb ∨ n.2 < Nb) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rb → ‖Y‖ < rb →
            Summable (fun m : ℕ × ℕ => ‖A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Db₁.eval X * Db₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pb)
        ) →
      ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Dt₁.eval 0 ≠ 0 ∧ Dt₂.eval 0 ≠ 0 ∧ 0 < rt ∧
          (∀ n : ℤ × ℤ, (n.1 < Nt ∨ n.2 < Nt) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rt → ‖Y‖ < rt →
            Summable (fun m : ℕ × ℕ => ‖A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Dt₁.eval X * Dt₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pt)
        ) →
      ∀ s : ℂ,
        m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) *
            ((Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) =
          m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹) ^ ℓ)⁻¹) * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) +
              ((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (V) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s)) := by sorry
