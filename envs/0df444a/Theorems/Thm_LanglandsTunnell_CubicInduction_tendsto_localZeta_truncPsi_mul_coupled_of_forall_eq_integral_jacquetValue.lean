-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
-- name    : LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/223fd62e-b1ae-594c-93f6-171bc0c707ce
-- title:
--   Dual local zeta integral as a limit of truncated coupled integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the completion, $|\cdot|$ for the modulus, $\psi_v$ for the standard local additive character, $dt$ for the self-dual Haar measure and $d^{\times}t=|t|^{-1}dt$ for the associated measure on $\mathbb{Q}_v\setminus\{0\}$, with $Z(f,\eta,s)=\int f\,\eta\,|\cdot|^{s}\,d^{\times}t$ (characters being extended by $0$ at $0$). Let $\nu_0,\nu_1,\nu_2$ and $\chi$ be locally constant characters of $\mathbb{Q}_v^{\times}$ with values in $\mathbb{C}^{\times}$, let $\Phi$ on $\mathbb{Q}_v^{3}$ be locally constant with compact support, assume $\lvert(\nu_i\chi)(\varpi)\rvert=1$ for the chosen uniformiser unit $\varpi$ and all $i$, and let $s$ satisfy $0<\operatorname{Re}s<1$. Let $F:\mathbb{Q}_v\to\mathbb{C}$ satisfy, for every unit $a$, $F(a)=|a|^{-1}\int_{\mathbb{Q}_v}W\bigl(w_\ell\cdot{}^{t}\bigl(\iota(\mathrm{diag}(a,1))\,u^-(x)\,(w'\cdot{}^{t}1^{-1})\bigr)^{-1}\cdot w_0\bigr)\,dx$, where $w_\ell$, $w'$, $w_0$ are the anti-identity, the transposition of the last two coordinates and the antidiagonal element of $\mathrm{GL}_3(\mathbb{Q}_v)$, $\iota(\mathrm{diag}(a,1))=\mathrm{diag}(a,1,1)$, $u^-(x)$ is the lower unipotent with entry $x$ in position $(2,1)$, ${}^{t}g^{-1}$ denotes the transpose-inverse, and $W(g)$ is the stabilised truncated Whittaker integral `jacquetValue` of the right translate by $g$ of the big-cell section $\mathbf{1}_{\mathrm{bigCell}}\cdot(\text{cell value at }\nu)\cdot\Phi(\text{cell ratio})$ attached to $(\nu,\Phi)$. Assume further that $x\mapsto F(x)\chi^{-1}(x)|x|^{1-s}$ is integrable for $d^{\times}x$. Then, as $c\to\infty$ over $\mathbb{Z}$, the product of $Z\bigl(t\mapsto \psi_v(-t)\mathbf{1}[v(-t)\le \exp c],(\nu_0\chi)^{-1},1-s\bigr)$, of the same quantity with $\nu_1$ in place of $\nu_0$, and of $$\int \Phi(p_1,p_2,p_3)\,(\nu_2\chi)^{-1}(p_1)|p_1|^{1-s}\,(\nu_1\chi)(p_2)|p_2|^{s}\,(\nu_0\nu_1^{-1})(p_2-p_1p_3)\,|p_2-p_1p_3|^{-1}\,\psi_v\!\left(\tfrac{p_3}{p_2-p_1p_3}\right)\mathbf{1}\!\left[v\!\left(\tfrac{p_3}{p_2-p_1p_3}\right)\le \exp c\right] d^{\times}p_1\,d^{\times}p_2\,dp_3$$ converges to $Z(F,\chi^{-1},1-s)$.
--
--   This is the local limit computation identifying the dual Tate zeta integral of the Jacquet-value function $F$ with a product of two truncated Gauss-type zeta integrals and one coupled three-variable integral, at a finite place, inside the cubic induction for $\mathrm{GL}_3$. It is used by [`LanglandsTunnell.CubicInduction.localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip`](thm.html#LanglandsTunnell.CubicInduction.localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip) to obtain the local functional-equation relation in the strip $0<\operatorname{Re}s<1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (F : v.adicCompletion ℚ → ℂ)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ,
      letI := localBorel ℚ v
      F a =
        (∫ x : v.adicCompletion ℚ,
            jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ))
          ∂(selfDualHaarAt ℚ v)) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (hint :
      letI := localBorel ℚ v
      Integrable (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
        (mulMeasure (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    Filter.Tendsto
      (fun c : ℤ =>
        localZeta (selfDualHaarAt ℚ v)
            (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 0 * χ)⁻¹ (1 - s) *
          localZeta (selfDualHaarAt ℚ v)
            (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 1 * χ)⁻¹ (1 - s) *
          (∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
              Φ ![p.1, p.2.1, p.2.2] *
                (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
                (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
                (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) *
                  ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
                (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
                  (psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ)
                else 0)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))))
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) F χ⁻¹ (1 - s))) := by sorry
