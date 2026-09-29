-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
-- name    : LanglandsTunnell.CubicInduction.middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b782e5eb-f12e-5858-9da8-7eb716a8eb58
-- title:
--   Primal–dual middle datum comparison: a γ-factor identity
-- statement:
--   Throughout, $v$ is a height-one prime of $\mathcal O_{\mathbb Q}$, $q=\mathrm{absNorm}(v)$ denotes the absolute norm of $v$, $\mathbb Q_v$ the completion of $\mathbb Q$ at $v$ with its valuation ring, $\mathrm{LocalGL3}\,v=\mathrm{GL}_3(\mathbb Q_v)$, and $\iota=$ `iotaGL` is the embedding $\mathrm{GL}_2\to\mathrm{GL}_3$, $M\mapsto\mathrm{diag}(M,1)$. Measures on $\mathbb Q_v$ are taken for the Borel $\sigma$-algebra `localBorel`; $\nu=$ `selfDualHaarAt ℚ v` is the self-dual additive Haar measure, $\mu^\times$ is the multiplicative measure `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))` on $\mathbb Q_v^\times$, $\mathrm{vol}(\mathcal O)=\nu^{\mathbb R}\{x:|x|_v\le 1\}$ and $\mathrm{vol}(\mathcal O^\times)=\mu^\times\{e:|e|_v=1\}$ (real-valued). Finally `weylPrime3` is the permutation matrix $w'$ exchanging the last two coordinates, `longWeyl3` the one, $w_0$, exchanging the first and third, `transposeInv3` is $g\mapsto{}^t(g^{-1})$, and `dualWhittakerFn3` $W$ is $g\mapsto W(w_0\,{}^t(g^{-1}))$.
--
--   The data are: an additive character $\psi_v$ of $\mathbb Q_v$ with $\psi_v=(\,$`psiLocal ℚ v`$\,)^{-1}$ (hypothesis `hψinv`); a function $W:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ subject to the following Whittaker hypotheses: $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z$ and $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ (`hW`), $W(1)=1$ (`hW1`), the multiplicity-one condition `hmult` that the space of $\psi_v$-Whittaker functionals on the cyclic subrepresentation $\mathrm{gl3CyclicSubspace}\,W$ (the $\mathbb C$-span of the right translates of $W$) has rank at most $1$, the condition `hirr` that every $F\ne 0$ in that cyclic subspace has $W$ in its own cyclic subspace, smoothness `hsm` (some open subgroup $U_v\le\mathrm{GL}_3(\mathbb Q_v)$ satisfies $W(gk)=W(g)$ for $k\in U_v$), and admissibility `hadm` (for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $U_v$-right-invariant element of the cyclic subspace of $W$ lies in the $\mathbb C$-span of $B$).
--
--   A gauge hypothesis `hWgauge` is imposed on $W$: there are $B\in\mathbb R$, $t\in\mathbb N$, $C\in\mathbb R$ such that, writing $\delta(h)=\mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $\delta'(h)=\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ for the norms of the determinant, of the last row, and of the $2\times2$ minors of the bottom two rows of $h$, one has $W(h)=0$ whenever the conjunction $\delta(h)\le B\wedge\delta'(h)\le B$ fails, and $\|W(h)\|\le C/(\delta(h)\delta'(h))^t$ whenever it holds.
--
--   A central character is given: a homomorphism $\omega_v:\mathbb Q_v^\times\to\mathbb C^\times$ which is unitary, $\|\omega_v(z)\|=1$ (`hωu`), and satisfies $W(t\cdot I_3\,h)=\omega_v(t)W(h)$ for all $t\in\mathbb Q_v^\times$ and $h$ (`hω`). A uniformiser is given: $\varpi$ in the valuation ring with nonzero image in $\mathbb Q_v$ (`hπ`) and $|\varpi|_v=\exp(-1)$ (`hϖ`); $\omega_v(\varpi)$ below means $\omega_v$ applied to the unit determined by this image.
--
--   Polynomials $E,E^\vee\in\mathbb C[T]$, a scalar $\varepsilon\in\mathbb C$ and $\ell\in\mathbb N$ enter through the local functional-equation hypothesis `h31`: for every $g\in\mathrm{GL}_3(\mathbb Q_v)$ there are $P:\mathbb C\to\mathbb C$ and $\sigma_0,\sigma_1\in\mathbb R$ such that (i) $P$ is rational in $q^{-s}$ up to a monomial, i.e. there are $Q,R\in\mathbb C[T]$ and $m\in\mathbb N$ with $R\ne0$ and $P(s)R(q^{-s})=Q(q^{-s})q^{ms}$ for all $s$; (ii) the rank-one integrand $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|_v^{s-1}$ is $\mu^\times$-integrable for $\mathrm{Re}\,s>\sigma_0$, and (iii) its integral `localZeta30` equals $E(q^{-s})^{-1}P(s)$ there; (iv) the two-variable integrand $(a,x)\mapsto \mathrm{dualWhittakerFn3}\,W(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,w'\,{}^t(g^{-1}))\,|a|_v^{s-1}$ is $\mu^\times\otimes\nu$-integrable for $\mathrm{Re}\,s>\sigma_1$, where $n_{21}(x)$ is the lower unipotent matrix with entry $x$ in position $(2,1)$; and (v) for $\mathrm{Re}(1-s)>\sigma_1$, `localZetaDual31` at $1-s$ and $g$ equals $E^\vee\!\big(q^{-(1-s)}\big)^{-1}\big(\varepsilon\,q^{\ell(1/2-s)}\big)P(s)$.
--
--   The vector under consideration is $V:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ lying in the cyclic subspace of $W$ (`hVmem`) and invariant under right translation by $\iota(k)$ for $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $\mathrm{GL}_2(\mathbb Q_v)$ pulled back along the local embedding from the level-one congruence subgroup of $\mathrm{GL}_2$ of the finite adeles for the unit ideal (`hVK`), and such that $\mathrm{dualWhittakerFn3}\,V$ is invariant in the same sense (`hVdK`). Further scalars are $a_1,a_2,u\in\mathbb C$ and $c_K\in\mathbb R$ with $a_1a_2\ne0$ (`ha`) and $c_K>0$ (`hcK`), together with polynomials $m_1^P,m_2^P$ and $k_P\in\mathbb Z$, and $m_1^D,m_2^D$ and $k_D\in\mathbb Z$.
--
--   For a right translate $g_0$ of the torus orbit, the Mellin array attached to $g_0$ is $A(n)=V\big(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1},1))\,g_0\big)=V\big(\mathrm{diag}(\varpi^{n_1+n_2},\varpi^{n_2},1)\,g_0\big)$ for $n=(n_1,n_2)\in\mathbb Z^2$. The rationality package for data $(N,D_1,D_2,\Pi,r)$ with $N\in\mathbb Z$, $D_1,D_2\in\mathbb C[T]$, $\Pi\in\mathbb C[T_1,T_2]$, $r\in\mathbb R$ asserts: $D_1(0)\ne0$, $D_2(0)\ne0$, $r>0$, $A(n)=0$ whenever $n_1<N$ or $n_2<N$, and for all $X,Y$ with $\|X\|,\|Y\|<r$ the family $\|A(N+m_1,N+m_2)X^{m_1}Y^{m_2}\|$ is summable over $(m_1,m_2)\in\mathbb N^2$ and $\big(\sum_{m}A(N+m_1,N+m_2)X^{m_1}Y^{m_2}\big)D_1(X)D_2(Y)=\Pi(X,Y)$.
--
--   Write $X_P=\big(a_1q^{-u}q^{-1/2}\big)q^{1-s}$, $Y_P=\big(a_2q^{u}q^{-1/2}\big)^{-1}\omega_v(\varpi)^{-1}q^{s}$, $X_D=\big(q^{1/2}(a_1q^{-u})^{-1}\big)^{-1}q^{1-s}$, $Y_D=\big(q^{1/2}(a_2q^{u})^{-1}\big)\omega_v(\varpi)^{-1}q^{s}$, and
--   $$C_P(s)=\Big(c_K\,\mathrm{vol}(\mathcal O)^2\,\mathrm{vol}(\mathcal O)\,\mathrm{vol}(\mathcal O^\times)^2\big(\mathrm{vol}(\mathcal O)\,(1-q^{-1}(a_1q^{-u})(a_2q^{u})^{-1})\big)^{-1}\Big)\varepsilon^{-1}q^{-\ell/2}\big(a_2q^{u}q^{-1/2}q^{-s}\big)^{-\ell}E\big(a_1q^{-u}q^{-(s+1/2)}\big)E^\vee\big((a_2q^{u})^{-1}q^{-(1/2-s)}\big),$$
--   $$C_D(s)=\Big(c_K\,\mathrm{vol}(\mathcal O)\,\mathrm{vol}(\mathcal O^\times)^2\big(\mathrm{vol}(\mathcal O)\,(1-q^{-1}(a_1q^{-u})(a_2q^{u})^{-1})\big)^{-1}\big(\big(q^{1/2}(a_1q^{-u})^{-1}\big)^{\ell}\big)^{-1}\Big)\varepsilon\,q^{\ell(1/2-s)}E\big(a_1q^{-u}q^{-(s+1/2)}\big)E^\vee\big((a_2q^{u})^{-1}q^{-(1/2-s)}\big).$$
--
--   The assertion is the implication of the following two hypotheses.
--
--   Primal middle datum: for all $(N_b,D^b_1,D^b_2,\Pi_b,r_b)$ satisfying the rationality package for the array attached to $g_0=w_0w'$, and all $(N_t,D^t_1,D^t_2,\Pi_t,r_t)$ satisfying it for the array attached to $g_0=w'$, one has for every $s\in\mathbb C$
--   $$m_1^P(q^{-s})\,q^{k_Ps}\cdot\big(D^b_1(X_P)D^b_2(Y_P)\big)\big(D^t_1(X_P)D^t_2(Y_P)\big)\cdot q= m_2^P(q^{-s})\,C_P(s)\Big(X_P^{N_b}Y_P^{N_b}\Pi_b(X_P,Y_P)\,D^t_1(X_P)D^t_2(Y_P)\,q\;+\;1\cdot X_P^{N_t}Y_P^{N_t}\Pi_t(X_P,Y_P)\,D^b_1(X_P)D^b_2(Y_P)\Big).$$
--
--   Dual middle datum: for all $(N_b,D^b_1,D^b_2,\Pi_b,r_b)$ satisfying the rationality package for the array attached to $g_0=w'\,\iota(\varpi^{\ell}I_2)$, and all $(N_t,D^t_1,D^t_2,\Pi_t,r_t)$ satisfying it for the array attached to $g_0=w_0w'\,\iota(\varpi^{\ell}I_2)$ (so that the roles of the two Weyl translates are interchanged with respect to the primal case), one has for every $s\in\mathbb C$
--   $$m_1^D(q^{-s})\,q^{k_Ds}\cdot\big(D^b_1(X_D)D^b_2(Y_D)\big)\big(D^t_1(X_D)D^t_2(Y_D)\big)(1-q^{-1})= m_2^D(q^{-s})\,C_D(s)\Big(X_D^{N_b}Y_D^{N_b}\Pi_b(X_D,Y_D)\,D^t_1(X_D)D^t_2(Y_D)\,(1-q^{-1})\;+\;\big((1-q^{-1})q^{-1}\big)X_D^{N_t}Y_D^{N_t}\Pi_t(X_D,Y_D)\,D^b_1(X_D)D^b_2(Y_D)\Big).$$
--
--   Under these two hypotheses the conclusion is: for every $s\in\mathbb C$,
--   $$m_1^D(q^{-s})\,q^{k_Ds}\,m_2^P(q^{-s})=\varepsilon^{2}\,\big(m_1^P(q^{-s})\,q^{k_Ps}\big)\,m_2^D(q^{-s}).$$
--
--   This is the comparison step of the local $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg functional equation at a finite place: the $\gamma$-factor extracted from the unfolded primal integral and the one extracted from the dual integral are shown to agree up to the factor $\varepsilon^2$, the two sides being linked by the interchange of the bulk and tail Mellin arrays under $s\mapsto 1-s$ together with the $\ell$-shift by $\varpi^\ell I_2$. It is used in the derivation of the functional equation for the Rankin–Selberg local integrals of the cubic-induction construction, namely by [`LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
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
    (a₁ a₂ u : ℂ) (cK : ℝ) (ha : a₁ * a₂ ≠ 0) (hcK : 0 < cK)
    (m₁P m₂P : Polynomial ℂ) (kP : ℤ) (m₁d m₂d : Polynomial ℂ) (kd : ℤ) :
    letI := localBorel ℚ v
    (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3))) (iotaGL (UnramifiedWhittaker.scalarPi
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
          (fun x : LocalGL3 v => V (x * weylPrime3)) (iotaGL (UnramifiedWhittaker.scalarPi
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
        m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s) *
            ((Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ))) =
          m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹) * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ)) +
              ((1 : ℂ)) * ((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →
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
              ((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →
    ∀ s : ℂ, m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) * m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
      ε ^ 2 * (m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s)) * m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
