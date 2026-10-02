-- Prove2me | Theorems.Thm_LeblSCV_Levi_levi_normal_form
-- name    : LeblSCV.Levi.levi_normal_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:27:26.062116+00:00
-- url     : https://prove2.me/theorems/664cf315-999b-4ec2-aa06-5877afe7fc23
-- title:
--   Lemma 2.3.9 — quadratic normal form of a real hypersurface
-- statement:
--   Let $M \subset \mathbb{C}^n$ be a smooth real hypersurface and $p \in M$. Write the coordinates as $(z, w) \in \mathbb{C}^{n-1} \times \mathbb{C}$. There is a local biholomorphic change of coordinates taking $p$ to $0$ and $M$ to the hypersurface
--   $$\operatorname{Im} w = \sum_{k=1}^{\alpha} |z_k|^2 - \sum_{k=\alpha+1}^{\alpha+\beta} |z_k|^2 + E(z, \bar z, \operatorname{Re} w),$$
--   with $\alpha + \beta \le n - 1$ and $E$ vanishing at the origin together with all its derivatives of order $1$ and $2$ ($E$ is $O(3)$). If $M = \partial U$ for an open set $U$ with smooth boundary, the coordinates can be chosen so that, in addition, $U$ is given by replacing $=$ with $>$, and then $\alpha$ and $\beta$ are the numbers of positive and negative eigenvalues of the Levi form of $U$ at $p$.
--
--   **Formalization Note.** $n = m + 1$, so the ambient space is `Fin (m + 1) → ℂ`; $z_k$ is coordinate `Fin.castSucc k` (0-based, so $k \le \alpha$ becomes `k.val < α`) and $w$ is coordinate `Fin.last m`. No generality is lost: $\mathbb{C}^0$ contains no hypersurface. The change of coordinates is `f` with `IsBiholomorphicOn f V V'`, `V ∋ p` and `V' ∋ 0` open, and the image of $M \cap V$ (resp. $U \cap V$) is exactly the displayed set within `V'`. $E$ is a real function of $(z, \operatorname{Re} w) \in \mathbb{C}^m \times \mathbb{R}$, and $O(3)$ is `VanishesToOrder 3 E 0`. In the boundary case $\alpha$, $\beta$ equal `leviPosIndex r p`, `leviNegIndex r p` for every defining function $r$ of $U$ at $p$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 73, Lemma 2.3.9

import Mathlib
import Definitions.Def_LeblSCV_Levi_IsSmoothHypersurface
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_leviPosIndex
import Definitions.Def_LeblSCV_Levi_IsBiholomorphicOn
import Definitions.Def_LeblSCV_Levi_VanishesToOrder

namespace LeblSCV.Levi

/-- Lemma 2.3.9 (Lebl, p. 73), in `ℂ^{m+1}` with coordinates `(z, w)`, `z_k = x (Fin.castSucc k)`
(`k < m`, 0-based) and `w = x (Fin.last m)`. Part 1: every smooth real hypersurface `M` is, after
a local biholomorphic change of coordinates `f : V → V'` taking `p` to `0`, given in `V'` by
`Im w = ∑_{k<α} |z_k|² − ∑_{α≤k<α+β} |z_k|² + E(z, Re w)` with `E` `O(3)` at the origin. Part 2:
if `M = ∂U` for an open `U` with smooth boundary, the coordinates can be chosen so that moreover
`f(U ∩ V)` is given by `>`, and `α`, `β` are the numbers of positive and negative eigenvalues of
the Levi form of `U` at `p` (for every defining function). -/
theorem levi_normal_form {m : ℕ} (M : Set (Fin (m + 1) → ℂ)) (hM : IsSmoothHypersurface M)
    (p : Fin (m + 1) → ℂ) (hp : p ∈ M) :
    (∃ (V V' : Set (Fin (m + 1) → ℂ)) (f : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ)),
      IsOpen V ∧ p ∈ V ∧ IsOpen V' ∧ (0 : Fin (m + 1) → ℂ) ∈ V' ∧ IsBiholomorphicOn f V V' ∧
      f p = 0 ∧ ∃ (α β : ℕ) (E : (Fin m → ℂ) × ℝ → ℝ), α + β ≤ m ∧ VanishesToOrder 3 E 0 ∧
        f '' (M ∩ V) = {x | x ∈ V' ∧ (x (Fin.last m)).im =
          (∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < α), ‖x (Fin.castSucc k)‖ ^ 2) -
          (∑ k ∈ Finset.univ.filter (fun k : Fin m => α ≤ k.val ∧ k.val < α + β),
              ‖x (Fin.castSucc k)‖ ^ 2) +
          E (fun k => x (Fin.castSucc k), (x (Fin.last m)).re)}) ∧
    (∀ U : Set (Fin (m + 1) → ℂ), HasSmoothBoundary U → frontier U = M →
      ∃ (V V' : Set (Fin (m + 1) → ℂ)) (f : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ)),
        IsOpen V ∧ p ∈ V ∧ IsOpen V' ∧ (0 : Fin (m + 1) → ℂ) ∈ V' ∧ IsBiholomorphicOn f V V' ∧
        f p = 0 ∧ ∃ (α β : ℕ) (E : (Fin m → ℂ) × ℝ → ℝ), α + β ≤ m ∧ VanishesToOrder 3 E 0 ∧
          f '' (M ∩ V) = {x | x ∈ V' ∧ (x (Fin.last m)).im =
            (∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < α), ‖x (Fin.castSucc k)‖ ^ 2) -
            (∑ k ∈ Finset.univ.filter (fun k : Fin m => α ≤ k.val ∧ k.val < α + β),
                ‖x (Fin.castSucc k)‖ ^ 2) +
            E (fun k => x (Fin.castSucc k), (x (Fin.last m)).re)} ∧
          f '' (U ∩ V) = {x | x ∈ V' ∧ (x (Fin.last m)).im >
            (∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < α), ‖x (Fin.castSucc k)‖ ^ 2) -
            (∑ k ∈ Finset.univ.filter (fun k : Fin m => α ≤ k.val ∧ k.val < α + β),
                ‖x (Fin.castSucc k)‖ ^ 2) +
            E (fun k => x (Fin.castSucc k), (x (Fin.last m)).re)} ∧
          ∀ (W : Set (Fin (m + 1) → ℂ)) (r : (Fin (m + 1) → ℂ) → ℝ),
            IsDefiningFunction U p W r → α = leviPosIndex r p ∧ β = leviNegIndex r p) := by sorry

end LeblSCV.Levi
