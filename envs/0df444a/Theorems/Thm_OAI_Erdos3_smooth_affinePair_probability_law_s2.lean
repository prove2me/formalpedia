-- Prove2me | Theorems.Thm_OAI_Erdos3_smooth_affinePair_probability_law_s2
-- name    : OAI.Erdos3.smooth_affinePair_probability_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:30:58.301099+00:00
-- url     : https://prove2.me/theorems/e40b3da2-96c0-4bd3-a1a3-5fd90749664c
-- title:
--   Local law of the pair of affine forms with smooth integer coefficients, up to an explicit error
-- statement:
--   Let $J$ be a finite type with decidable equality, let $t, u : J \to \mathbb{Z}$, and let $k \in J$ with $u_k - t_k \ne 0$. Let $H, L, C, \kappa, \delta$ be reals and $Q$ a natural number with $H > 0$, $L \ge 1$, $C \ge 1$, $\kappa > 0$ and $0 \le \delta \le 1$. Write $J' = \{j \in J : j \ne k\}$ and $g$ = `BohrLattice.Primitive.content (u - t)`, the gcd of the integers $u_j - t_j$ (defined by OpenAI). Assume:
--   - $|t_j / L| \le C$ and $|u_j / L| \le C$ for all $j$;
--   - $\kappa \le |(u_k - t_k)/L|$;
--   - $|g| \le Q$;
--   - $|u_k - t_k| \cdot L / H \le \delta$;
--   - $4^{2 + |J'|} \cdot \lambda_k \cdot \delta \le 1/2$, where $\lambda_k$ = `smoothPairRowLipschitz k` $= (|J'| + 2) \cdot$ `probabilityProfileLipschitz` (constants of OpenAI).
--
--   Let $f$ = `splitSmoothProductProfile J' (Fin 2)`, the function $(y, w) \mapsto \phi_{J'}(y)\, \phi_{\operatorname{Fin} 2}(w)$ on $\mathbb{R}^{J'} \times \mathbb{R}^2$, where $\phi$ is OpenAI's smooth product profile (with values in $[0,1]$, vanishing outside a ball). Let $S = (H, H/L)$ (`affinePairScale H L`) and let $T$ be the constant $H/L$ on $J'$. Then the scaled input mass `scaledInputMass f S T` $= \bigl(\sum_{(a, y) \in \mathbb{Z}^2 \times \mathbb{Z}^{J'}} f(y/T, a/S)\bigr) / \bigl((\prod_i S_i)(\prod_j T_j)\bigr)$ is positive, and for every $v \in \mathbb{Z}^2$,
--   $$\Bigl| H^2 \cdot \pi(v) - \mathbf{1}[g \mid v_1 - v_0] \cdot |g| \cdot \rho\bigl(v / H\bigr) \Bigr| \le E \cdot \delta.$$
--   Here:
--   - $\pi$ = `integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f … S T …` is the probability mass function on $\mathbb{Z}^2$ obtained by drawing $(a, y) \in \mathbb{Z}^2 \times \mathbb{Z}^{J'}$ with probability proportional to $f(y/T, a/S)$ (coordinatewise division) and taking $\begin{pmatrix} 1 & t_k \\ 1 & u_k \end{pmatrix} a + \begin{pmatrix} t|_{J'} \\ u|_{J'} \end{pmatrix} y$, i.e. the pair $\bigl(a_0 + t_k a_1 + \sum_{j \in J'} t_j y_j,\ a_0 + u_k a_1 + \sum_{j \in J'} u_j y_j\bigr)$; $\pi(v)$ is taken as a real number;
--   - $\rho$ = `affinePairRowDensity t u k hne H L _ _ f`, OpenAI's normalized fiber density on $\mathbb{R}^2$ built from the same matrices, scales and profile; $v/H$ is coordinatewise;
--   - $E$ = `normalizedFiberErrorConstant 2 |J'| Q (4C/κ) (|J| C) 1 1 λ_k`, an explicit constant of OpenAI.
--
--   Lean: `OAI.Erdos3.smooth_affinePair_probability_law_s2`, which states OpenAI's `OAI.Erdos3.smooth_affinePair_probability_law` (in `lean/OAI/Combinatorics/Progressions/Lattices/SmoothAffinePairLaw.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B085`, `OAIE3v2B086` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/SmoothAffinePairLaw.lean (declaration OAI.Erdos3.smooth_affinePair_probability_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085
import Definitions.Def_OAIE3v2B086

section

namespace OAI

namespace Erdos3

open scoped NNReal Matrix

theorem smooth_affinePair_probability_law_s2 {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) :
    let f := splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L), ∀ v,
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f
          (fun z => (splitSmoothProductProfile_range _ _ z).1)
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL))
          (splitSmoothProductProfile_zero_outside _ _) hM v).toReal -
        (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
          ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
            affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
              (fun i => (v i : ℝ) / H) else 0)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) 1 1 (smoothPairRowLipschitz k) * δ := by
  sorry

end Erdos3

end OAI
end
