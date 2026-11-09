-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_lemma_5
-- name    : LinMatroidSecretary.Online.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:37.355477+00:00
-- url     : https://prove2.me/theorems/c849f062-b7ae-428e-b72c-6345f3d56192
-- title:
--   Lemma 5 — the dimension increment on safe states
-- statement:
--   Let $e$ be an element and $W$ a subspace with $v_e\notin W$ (in the paper: $e\in\mathrm{OPT}(X)$ and $W\in F_e=\{W\in\operatorname{supp}\mu_{X-e}: e\notin W\}$). Then for every subspace $L$,
--   $$\Delta_e(W,L)=\dim((W+\langle e\rangle)\cap L)-\dim(W\cap L)=\mathbf 1[v_e\in W+L].$$
--
--   Accepting $e$ in a safe state therefore raises $\dim(W\cap L)$ by one exactly when $e\in W+L$; this drives the greedy construction (8).
--
--   Differences from the source:
--   - generalization: e ∈ OPT(X) and W ∈ F_e = {W ∈ supp(µ_{X−e}) | e ∉ W} → any element e and any subspace W with v_e ∉ W; reason: every W ∈ F_e satisfies v_e ∉ W, which is the only property the identity uses; the Lean statement specializes to the source
--   - encoding: subspaces of the represented finite-dimensional space and the integer dimension difference Δ → Submodule F (Fin d → F), with Δ computed by subtraction of real casts of finrank; reason: choosing coordinates and casting finite dimensions changes no instance or equality
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Lemma 5, PDF p. 14 (printed p. 12)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

open Classical in
/-- Lemma 5 (PDF p. 14, printed 12), stated for every subspace `W` not containing `v e` (in
particular every `W ∈ F_e = {W ∈ supp µ_{X−e} : e ∉ W}` for `e ∈ OPT(X)`):
`∆_e(W, L) = 1[e ∈ W + L]` for every subspace `L`. -/
theorem lemma_5 {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι]
    [LinearOrder ι] (v : ι → Fin d → F) (e : ι) (W : Submodule F (Fin d → F)) (hW : v e ∉ W)
    (L : Submodule F (Fin d → F)) :
    Delta v e W L = if v e ∈ W ⊔ L then 1 else 0 := by sorry

end LinMatroidSecretary.Online
