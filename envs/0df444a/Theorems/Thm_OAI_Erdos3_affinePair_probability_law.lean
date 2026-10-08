-- Prove2me | Theorems.Thm_OAI_Erdos3_affinePair_probability_law
-- name    : OAI.Erdos3.affinePair_probability_law
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:38:25.770625+00:00
-- url     : https://prove2.me/theorems/22d86eb9-cdfd-41cb-a325-f98bc2eb313b
-- title:
--   Local law for the integer image of a smooth affine pair sample
-- statement:
--   Let $J$ be a finite type with decidable equality, $t,u\colon J\to\mathbb Z$ and $k\in J$ with $u_k-t_k\ne0$ (`hne`). Let $H,L,C,\kappa,R,F,\delta$ be reals, $Q\in\mathbb N$ and $K\ge0$, with $0<H$, $1\le L$, $1\le C$, $0<\kappa$, $0\le R$, $0\le F$, $0\le\delta\le1$, $|t_j/L|\le C$ and $|u_j/L|\le C$ for every $j\in J$, $\kappa\le|(u_k-t_k)/L|$, $g:=|\gcd_j(u_j-t_j)|\le Q$ (the content of $u-t$, `BohrLattice.Primitive.content`), and $|u_k-t_k|\,L/H\le\delta$. Let $f\colon\mathbb R^{\{j\ne k\}}\times\mathbb R^2\to\mathbb R$ be nonnegative, $K$-Lipschitz, zero outside the ball of radius $R$, with $\int f=1$ and $|f|\le F$, and assume $(2R+2)^{2+|\{j:j\ne k\}|}K\delta\le1/2$. Then there is a proof `hM` that `scaledInputMass f (affinePairScale H L) (fun _ => H / L)` is positive, such that for every $v\in\mathbb Z^2$,
--   $$\Big|H^2\,\pi(v)-\mathbf 1[g\mid v_1-v_0]\cdot g\cdot \texttt{affinePairRowDensity}\ t\ u\ k\ \mathit{hne}\ H\ L\ \ldots\ f\ (v/H)\Big|\le \texttt{normalizedFiberErrorConstant}\ 2\ |\{j:j\ne k\}|\ Q\ (4C/\kappa)\ (|J|C)\ R\ F\ K\cdot\delta .$$
--   Here $\pi$ is `integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f … hM`: the law of $A p+B q\in\mathbb Z^2$, with $A=\begin{pmatrix}1&t_k\\1&u_k\end{pmatrix}$ (`affinePairPivot`) and $B$ the $2\times\{j\ne k\}$ integer matrix with columns $(t_j,u_j)$ (`affinePairFree`), when $(p,q)\in\mathbb Z^2\times\mathbb Z^{\{j\ne k\}}$ is drawn with probability proportional to $f\big((q_j/(H/L))_j,\,(p_0/H,\,p_1/(H/L))\big)$ (`affinePairScale H L` $=(H,H/L)$); `scaledInputMass f S T` is $\sum_{(p,q)}f(q/T,p/S)$ divided by $\prod S\prod T$. `affinePairRowDensity` is a real function on $\mathbb R^2$ (a `normalizedFiberDensity` built from the same pivot, free columns and scales), and `normalizedFiberErrorConstant j d G U V R H K` is the real number $2\,\texttt{integerFiberErrorConstant}\ j\ d\ G\ U\ V\ R\ K+2\,G\,j!\,U^j\,H\,(2R)^d\,(2R+2)^{j+d}K$.
--
--   Lean: `OAI.Erdos3.affinePair_probability_law` in `lean/OAI/Combinatorics/Progressions/Lattices/SmoothAffinePairLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/SmoothAffinePairLaw.lean#L624

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem affinePair_probability_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ R F δ : ℝ} (Q : ℕ) (K : ℝ≥0)
    (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf : LipschitzWith K f)
    (hsupport : ∀ z, R < ‖z‖ → f z = 0) (hmass : (∫ z, f z) = 1)
    (hsmall : (2 * R + 2) ^ (2 + Fintype.card {j : J // j ≠ k}) * K * δ ≤ 1 / 2)
    (hbound : ∀ z, ‖f z‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L), ∀ v,
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f hf0
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v).toReal -
        (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
          ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
            (fun i => (v i : ℝ) / H) else 0)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) R F K * δ := by
  sorry

end Erdos3
end OAI
