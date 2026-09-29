-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.RankinSelberg.exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/560c6c9a-2e80-543a-876f-19ca870dbf0f
-- title:
--   Cleared local Rankin–Selberg functional equation at the family centre
-- statement:
--   Throughout, $p$ is a height-one prime of $\mathcal{O}_{\mathbb{Q}} = \mathbb{Z}$, $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, and $N =$ `Ideal.absNorm p.asIdeal` is the absolute norm of $p$. Write $\psi_p =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) for the standard local additive character, $\iota =$ `iotaGL` for the embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_3(F)$, $g \mapsto \mathrm{diag}(g,1)$ (via `embedMat2`), $n_3(x,y,z) =$ `upperUnipotent3 x y z` for the upper unipotent matrix with entries $x, y, z$, $\widetilde{W} =$ `dualWhittakerFn3 W`, i.e. $\widetilde W(g) = W(w_\ell \, {}^{t}g^{-1})$ with $w_\ell =$ `longWeyl3` and `transposeInv3`, and $\delta(g) =$ `modulus` of $\det g$, the module of the determinant (the distributive Haar character at $\det g$, and $0$ at $0$). The group $N_2$ is the range of `unipotentGL2Hom`, the upper unipotent subgroup of $\mathrm{GL}_2(F)$, parametrised by $x \mapsto$ `unipotent x` $= \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and [`RSCarrier.rsLocalIntegral μ₂ N₂ μN₂ δ s A B`](def/LanglandsTunnell_RSCarrier.html#L16) is the local Rankin–Selberg integral $\int (A(g)B(g))\,\delta(g)^{s-1/2}$ taken against $\mu_2$ weighted by the density [`HaarQuotient.density N₂ μN₂`](def/HaarQuotient.html#L25) attached to $\mu_{N_2}$. The measurable structure on $\mathrm{GL}_2(F)$ is the Borel one, `localGLBorel ℚ p`.
--
--   The data are: a family $E : \mathbb{Z} \to \mathrm{GL}_3(F) \to \mathbb{C}$; an open subgroup $U \le \mathrm{GL}_3(F)$; functions $\mathcal{W} : \mathbb{C} \to \mathrm{GL}_3(F) \to \mathbb{C}$ and $\mathcal{W}_c : \mathrm{GL}_3(F) \to \mathbb{C}$; a function $w$ on $\mathrm{GL}_2(F)$; an element $w_0 \in \mathrm{GL}_2(F)$; a function $\gamma : \mathbb{C} \to \mathbb{C}$ and an integer $e$; and clearing data consisting of finite sets $SQ, SQd \subseteq \mathbb{Z} \times \mathbb{Z}$ with coefficient functions $q, qd : \mathbb{Z} \times \mathbb{Z} \to \mathbb{C}$.
--
--   The hypotheses on the family are: `hElaw`, that every $E_i$ is a $\psi_p^{-1}$-Whittaker function, $E_i(n_3(x,y,z)\,g) = \psi_p(x+y)^{-1} E_i(g)$ for all $x,y,z \in F$ and $g$; `hEU`, that every $E_i$ is right invariant under the open subgroup $U$; and `hEfin`, local finiteness: for every compact $C \subseteq \mathrm{GL}_3(F)$ the set of indices $i$ with $E_i$ not identically zero on $C$ is finite. The two sums are prescribed pointwise by `hW`, $\mathcal{W}(u)(g) = \sum_{i \in \mathbb{Z}} N^{-iu} E_i(g)$, and `hWc`, $\mathcal{W}_c(g) = \sum_{i \in \mathbb{Z}} E_i(g)$, both as finite-support sums over $\mathbb{Z}$; thus $\mathcal{W}_c$ is the member of the family at $u = 0$.
--
--   The hypotheses on the $\mathrm{GL}_2$ partner are: `hwlaw`, the $\psi_p$-Whittaker law $w(\mathrm{unipotent}(x)\,g) = \psi_p(x)\,w(g)$; `hwsm`, the existence of an open subgroup $U_2 \le \mathrm{GL}_2(F)$ under which $w$ is right invariant; and `hw₀p`, that the underlying matrix of $w_0$ is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The assertion is universally quantified over Haar measures $\mu_2$ on $\mathrm{GL}_2(F)$ and $\mu_{N_2}$ on $N_2$, and has the form of a three-premiss implication.
--
--   The first premiss (the family-level cleared functional equation) asserts the existence of $u_0 \in \mathbb{R}$ such that for every real $u > u_0$ there are polynomials $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$, and reals $\sigma_2, \sigma_3$ with five clauses: (a) for $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto \mathcal{W}(u)(\iota g)\,w(g)\,\delta(g)^{s-1/2}$ is integrable for the weighted measure; (b) for $\mathrm{Re}\,s > \sigma_3$ the function $g \mapsto \widetilde{\mathcal{W}(u)}(\iota g)\,\delta(g)\,w(w_0\,{}^{t}g^{-1})\,\delta(g)^{s-1/2}$ is integrable; (c) for $\mathrm{Re}\,s > \sigma_2$,
--   $$\Psi\bigl(s; \mathcal{W}(u)\circ\iota,\,w\bigr)\cdot\Bigl(\sum_{(a,b) \in SQ} q(a,b)\,N^{-as}N^{-bu}\Bigr) = N^{ms}\,P(N^{-s}),$$ where $\Psi$ denotes [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with the above data; (d) for $\mathrm{Re}\,s > \sigma_3$ the same identity for the dual pair, $$\Psi\bigl(s; \widetilde{\mathcal{W}(u)}\circ\iota,\, g \mapsto \delta(g) w(w_0\,{}^{t}g^{-1})\bigr)\cdot\Bigl(\sum_{(a,b)\in SQd} qd(a,b)\,N^{-as}N^{-bu}\Bigr) = N^{m^\vee s}\,P^\vee(N^{-s});$$ and (e) for every $s \in \mathbb{C}$ the cleared functional equation between the resulting Laurent data,
--   $$N^{m^\vee s}P^\vee(N^{-s})\cdot\Bigl(\sum_{(a,b)\in SQ} q(a,b)\,N^{as}N^{-bu}\Bigr) = \bigl(\gamma(s)\,N^{eu}\bigr)\cdot\bigl(N^{-ms}P(N^{s})\bigr)\cdot\Bigl(\sum_{(a,b)\in SQd} qd(a,b)\,N^{-as}N^{-bu}\Bigr).$$
--   Note that $\gamma$ and $e$ are fixed in advance, independently of $u$, while $P, P^\vee, m, m^\vee, \sigma_2, \sigma_3$ may depend on $u$.
--
--   The second and third premisses are integrability at the centre: there is $\sigma_c$ such that for $\mathrm{Re}\,s > \sigma_c$ the function $g \mapsto \mathcal{W}_c(\iota g)\,w(g)\,\delta(g)^{s-1/2}$ is integrable, and there is $\sigma_d$ such that for $\mathrm{Re}\,s > \sigma_d$ the function $g \mapsto \widetilde{\mathcal{W}_c}(\iota g)\,\delta(g)\,w(w_0\,{}^{t}g^{-1})\,\delta(g)^{s-1/2}$ is integrable, both for the weighted measure.
--
--   The conclusion asserts the existence of polynomials $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ such that: first, for $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto \mathcal{W}_c(\iota g)\,w(g)\,\delta(g)^{s-1/2}$ is integrable for the weighted measure; second, for $\mathrm{Re}\,s > \sigma_3$ the function $g \mapsto \widetilde{\mathcal{W}_c}(\iota g)\,\delta(g)\,w(w_0\,{}^{t}g^{-1})\,\delta(g)^{s-1/2}$ is integrable; third, for $\mathrm{Re}\,s > \sigma_2$,
--   $$\Psi\bigl(s; \mathcal{W}_c\circ\iota,\, w\bigr)\cdot\Bigl(\sum_{(a,b)\in SQ} q(a,b)\,N^{-as}\Bigr) = N^{ms}\,P(N^{-s});$$ fourth, for $\mathrm{Re}\,s > \sigma_3$,
--   $$\Psi\bigl(s; \widetilde{\mathcal{W}_c}\circ\iota,\, g \mapsto \delta(g)w(w_0\,{}^{t}g^{-1})\bigr)\cdot\Bigl(\sum_{(a,b)\in SQd} qd(a,b)\,N^{-as}\Bigr) = N^{m^\vee s}\,P^\vee(N^{-s});$$ and fifth, for every $s \in \mathbb{C}$,
--   $$N^{m^\vee s}P^\vee(N^{-s})\cdot\Bigl(\sum_{(a,b)\in SQ} q(a,b)\,N^{as}\Bigr) = \gamma(s)\,\bigl(N^{-ms}P(N^{s})\bigr)\cdot\Bigl(\sum_{(a,b)\in SQd} qd(a,b)\,N^{-as}\Bigr).$$
--   Thus the clearing factors in the conclusion are the specialisations of the bivariate Laurent polynomials attached to $SQ, q$ and $SQd, qd$ at $N^{-u} = 1$, the twisting factor $N^{eu}$ has disappeared, and the gamma factor is the same function $\gamma$ as in the premiss.
--
--   This is the flat-section descent step in the local theory of Rankin–Selberg convolutions for $\mathrm{GL}_3 \times \mathrm{GL}_2$ over $\mathbb{Q}_p$: a cleared local functional equation, valid for all sufficiently large values of the flat-family parameter $u$ with one fixed gamma factor, is transported to the centre $u = 0$ of the family, where the clearing Laurent polynomials are specialised at $N^{-u} = 1$. It feeds the assembly of the global functional equation used in the converse-theorem input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
    (p : HeightOneSpectrum (𝓞 ℚ))

    (E : ℤ → LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
    (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)

    (W : ℂ → LocalGL3 p → ℂ) (Wc : LocalGL3 p → ℂ)
    (hW : ∀ (u : ℂ) (g : LocalGL3 p), W u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g)
    (hWc : ∀ g : LocalGL3 p, Wc g = ∑ᶠ i : ℤ, E i g)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U₂ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U₂ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U₂, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (γ : ℂ → ℂ) (e : ℤ)

    (SQ SQd : Finset (ℤ × ℤ)) (q qd : ℤ × ℤ → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u →
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W u (iotaGL g) * w g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 (W u) (iotaGL g) *
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W u (iotaGL g)) w *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 (W u) (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) *
                (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (γ s * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e : ℂ) * (u : ℂ))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))))) →

      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (Wc (iotaGL g) * w g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
      (∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (dualWhittakerFn3 Wc (iotaGL g) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (Wc (iotaGL g) * w g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (dualWhittakerFn3 Wc (iotaGL g) *
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => Wc (iotaGL g)) w *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 Wc (iotaGL g))
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) *
              (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s))) =
            γ s * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
              (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s))) := by sorry
