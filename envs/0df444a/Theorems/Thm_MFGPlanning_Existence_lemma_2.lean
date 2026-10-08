-- Prove2me | Theorems.Thm_MFGPlanning_Existence_lemma_2
-- name    : MFGPlanning.Existence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:39.411934+00:00
-- url     : https://prove2.me/theorems/343b333d-f6b8-45c7-b641-64f7e8746605
-- title:
--   Lemma 2 — $\Theta^*$, $\Sigma^*$ convex and l.s.c., with explicit formulas
-- statement:
--   Assume (24) and (G4). The functionals $\Theta^*$ and $\Sigma^*$ are convex and lower semicontinuous. Moreover,
--   $$\Theta^*(M,Z) = \sum_{n=1}^{N_T}\sum_{i,j}(W+\chi)(M^{n-1}_{i,j}) + \sup_\beta\Big\{\sum_{n=1}^{N_T}\sum_{i,j}\langle[Z^{n-1}]_{i,j},[\beta^n]_{i,j}\rangle - M^{n-1}_{i,j}\,g(x_{i,j},[\beta^n]_{i,j})\Big\},$$
--   where $(W+\chi)(m) = W(m)$ for $m\ge0$ and $+\infty$ otherwise, and, for any value of the auxiliary grid function $M^{N_T}$,
--   $$\Sigma^*(M,Z) = \sup_{\Psi:\ \sum_{i,j}\Psi^0_{i,j}=0}\Big\{\frac1{\Delta t}\sum_{i,j}\big((m_T)_{i,j}+M^{N_T}_{i,j}\big)\Psi^{N_T}_{i,j} - \frac1{\Delta t}\sum_{i,j}\big((m_0)_{i,j}+M^0_{i,j}\big)\Psi^0_{i,j}$$
--   $$\qquad + \sum_{n=0}^{N_T-1}\sum_{i,j}\Psi^{n+1}_{i,j}\Big(\frac{M^n_{i,j}-M^{n+1}_{i,j}}{\Delta t} - \nu(\Delta_hM^n)_{i,j} - \mathrm{div}_h(Z^n)_{i,j}\Big)\Big\}.$$
--
--   The two formulas turn the abstract dual problem into the primal control problem (26): $\Theta^*$ is the running cost and $\Sigma^*(-M,-Z)$ encodes the discrete Fokker–Planck constraint.
--
--   **Formalization Note** $M^{N_T}$ is not a variable of $\Sigma^*$, whose arguments are $M^0,\dots,M^{N_T-1}$; its two occurrences in the formula cancel, so the formula is asserted for every grid function $M^{N_T}$. The supremum over $\Psi$ ranges over $\Psi$ with $\sum_{i,j}\Psi^0_{i,j} = 0$, as forced by the definition (29) of $\Sigma$ and stated in the proof. Values are in `EReal`; convexity of $\Theta^*$, $\Sigma^*$ is convexity of their epigraphs. Of the standing assumptions, only (24) and (G4) are assumed.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), Lemma 2, p. 8, and its proof, p. 9

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Lemma 2 of Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 8 (PDF 9):
`Θ^*` and `Σ^*` are convex and lower semicontinuous;
`Θ^*(M, Z) = ∑_{n,i,j} (W + χ)(M^{n−1}_{i,j})
  + sup_β {∑_{n,i,j} ⟨[Z^{n−1}_{i,j}], [β^n]_{i,j}⟩ − M^{n−1}_{i,j} g(x_{i,j}, [β^n]_{i,j})}`, and
`Σ^*(M, Z) = sup_Ψ {(1/Δt) ∑ ((m_T) + M^{N_T}) Ψ^{N_T} − (1/Δt) ∑ ((m_0) + M^0) Ψ^0
  + ∑_{n=0}^{N_T−1} ∑ Ψ^{n+1} ((M^n − M^{n+1})/Δt − ν (Δ_h M^n) − div_h(Z^n))}`.

Formalization Note: stated under (24) and (G4). Convexity of the `EReal`-valued functionals is
convexity of their epigraphs. `M^{N_T}` is not a variable of `Σ^*` (its arguments are
`M^0, …, M^{N_T−1}`); its two occurrences in the page's formula cancel, so the formula is stated for
every value `Mlast` of `M^{N_T}`. The supremum over `Ψ` ranges over `Ψ` with `∑_{i,j} Ψ^0_{i,j} = 0`,
as in the definition (29) of `Σ`. -/
theorem lemma_2 (d : Data) (hW : A24 d) (hG4 : G4 d) :
    Convex ℝ {x : ((Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ)) × ℝ |
        ThetaStar d x.1.1 x.1.2 ≤ (x.2 : EReal)} ∧
    LowerSemicontinuous
        (fun x : (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) => ThetaStar d x.1 x.2) ∧
    Convex ℝ {x : ((Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ)) × ℝ |
        SigmaStar d x.1.1 x.1.2 ≤ (x.2 : EReal)} ∧
    LowerSemicontinuous
        (fun x : (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) => SigmaStar d x.1 x.2) ∧
    (∀ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ),
      ThetaStar d M Z =
        (∑ k, ∑ p, Wchi d (M k p)) +
          ⨆ β : Fin d.NT → d.Pt → Fin 4 → ℝ,
            (((∑ k, ∑ p, ((∑ l, Z k p l * β k p l) - M k p * d.g p (β k p))) : ℝ) : EReal)) ∧
    (∀ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ) (Mlast : d.Pt → ℝ),
      SigmaStar d M Z =
        ⨆ (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) (_ : ∑ p, Ψ 0 p = 0),
          ((((1 / d.dt) * ∑ p, (d.mT p + Mlast p) * Ψ (Fin.last d.NT) p
              - (1 / d.dt) * ∑ p, (d.m0 p + M 0 p) * Ψ 0 p
              + ∑ n : Fin d.NT, ∑ p, Ψ n.succ p *
                  ((M n p - Fin.snoc (α := fun _ => d.Pt → ℝ) M Mlast n.succ p) / d.dt
                    - d.ν * lap d (M n) p - divh d (Z n) p)) : ℝ) : EReal)) := by sorry

end MFGPlanning.Existence
