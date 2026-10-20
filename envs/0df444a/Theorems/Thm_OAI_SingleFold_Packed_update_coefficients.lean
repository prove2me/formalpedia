-- Prove2me | Theorems.Thm_OAI_SingleFold_Packed_update_coefficients
-- name    : OAI.SingleFold.Packed.update_coefficients
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:32:46.829505+00:00
-- url     : https://prove2.me/theorems/4876ec78-023f-4f27-a261-3ac86f217bc0
-- title:
--   Reading a counter update off a packed equation
-- statement:
--   For $B,k\in\mathbb{N}$ write $\mathrm{digit}_B(x,t)=\lfloor x/B^t\rfloor\bmod B$, $\mathrm{pack}_B(k,f)=\sum_{t<k}f(t)B^t$ and $\mathrm{ones}_B(k)=\mathrm{pack}_B(k,1)$. Let $2m\le B$, $d<m$, and let $r,a,f:\mathbb{N}\to\mathbb{N}$ with $r(t)<m$ for $t\le T$ and $a(t),f(t)\le1$ for $t<T$. If
--   $$
--   \mathrm{pack}_B(T+1,r)+B\,\mathrm{pack}_B(T,f)=d+B\bigl(\mathrm{pack}_B(T,r)+\mathrm{pack}_B(T,a)\bigr),
--   $$
--   then $r(0)=d$ and $r(t+1)+f(t)=r(t)+a(t)$ for all $t<T$.
--
--   In the counter system $r$ is a counter history, $a$ its increments and $f$ its decrements. One packed equation then encodes the whole update rule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean#L245-L276

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed

theorem OAI.SingleFold.Packed.update_coefficients {B T m d : ℕ} (hB : 2*m ≤ B) (hd : d < m)
    (r a f : ℕ → ℕ) (hr : ∀t < T+1,r t < m) (ha : ∀t < T,a t ≤ 1) (hf : ∀t < T,f t ≤ 1)
    (he : pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a)) :
    r 0=d ∧ ∀t < T,r (t+1)+f t=r t+a t := by sorry
