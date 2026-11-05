-- Prove2me | Theorems.Thm_MayersQKD_sampling_bound
-- name    : MayersQKD.sampling_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:52.336823+00:00
-- url     : https://prove2.me/theorems/093dc480-cfb9-4ede-a9f8-dfde5230cda9
-- title:
--   §10, p.14 — sampling bound $\Pr(J[E_c,\epsilon]=0\wedge J[T_0\cap R,\delta]=1)\le2^{-4\gamma n}$ (corrected: $J=1$ on the close side)
-- statement:
--   Let $0\le\delta<\epsilon$ and $\gamma>0$ with $6\gamma\le(\epsilon-\delta)^2$. Fix an attack, a seed and a value of $c$. Let $\theta$ and $R$ be uniform, let $\alpha$ be uniform, and let $\hat w$ have probability $\|M_{\hat w}|\psi_{\alpha,\hat\theta}\rangle\|^2$. Then
--
--   $$
--   \Pr\bigl(d_{E_c}(\alpha,\hat w)>\epsilon n\ \wedge\ d_{T_0\cap R}(\alpha,\hat w)\le\delta n\bigr)\le2^{-4\gamma n}.
--   $$
--
--   In words, it is exponentially unlikely that $\alpha$ is close to $\hat w$ on the tested positions and far from it on $E_c$. Here $E_c$ is any set the rule produces from the seed, $\hat w$, $R$, $\theta$.
--
--   Differences from the source:
--   - correction: J[E, τn] = 0 if and only if d_E(α, ŵ) ≤ τn → J[E, τn] = 1 if and only if d_E(α, ŵ) ≤ τn; reason: with the printed sign, Pass = J[T₀ ∩ R, δn] would be 1 exactly when more than δn errors occur, contrary to step 5; the event on p.14 is the intended one once J is fixed
--   - reading: printed γ = 10⁻⁶ with "an appropriate ε > δ" → every γ > 0 and 0 ≤ δ < ε with 6γ ≤ (ε − δ)²; reason: the paper leaves ε unspecified; 6 is this formalization’s explicit reading of "appropriate"
--   - generalization: the single value γ = 10⁻⁶ → all γ > 0 subject to 6γ ≤ (ε − δ)²; reason: specializes to the printed γ whenever ε − δ ≥ 0.00245
--   - encoding: a fixed θ̂ (§6) → a fixed seed of the attack, which fixes θ̂; reason: the seed is the mixed-attack version of the same convention
--   - generalization: P₀ for the E_c of the run → a separate statement for each value of c; reason: P₀ depends on E_c; the bound for each c implies the bound for c uniform
--   - encoding: E_c always exists → if the rule stops, E_c is ∅ and the event is empty; reason: in that case nothing is announced (§5, step 6 cannot be carried out)
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §10, p.14

import Mathlib
import Definitions.Def_MayersQKD_condLaw
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_Lsub
import Definitions.Def_MayersQKD_testEffect

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §10, p.14: in the picture of p.13,
`Pr(J[E_c, ε] = 0 ∧ J[T₀ ∩ R, δ] = 1) ≤ 2^(−4γn)` "for an appropriate `ε > δ`".

**Formalization Note.** Stated for every `γ > 0` and `0 ≤ δ < ε` with `6γ ≤ (ε − δ)²`, for each fixed
seed and each `c`. The printed `γ = 10⁻⁶` is an instance. The constant `6` is this formalization's
reading of "appropriate". -/
theorem sampling_bound {n r m : ℕ} (δ ε γ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε) (hγ : 0 < γ)
    (h6 : 6 * γ ≤ (ε - δ) ^ 2) (A : Attack n r m) (s : A.Seed) (c : Bool) :
    mass (alphaWeight A s) (fun x =>
        ¬ J (EcOf A s x.2.2.1 x.2.1 x.1 c) (ε * n) x.2.2.2 x.2.2.1 ∧
        J (T0 x.1 (A.commit s) ∩ x.2.1) (δ * n) x.2.2.2 x.2.2.1) ≤
      (2 : ℝ) ^ (-(4 * γ * n)) := by sorry

end MayersQKD
